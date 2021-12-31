{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Lift.BiKey where

import "base" Data.Char
import "base" Data.Data qualified as DD
import "base" Data.Foldable (toList)
import "base" Data.List
import "base" Data.Maybe (fromMaybe)
import "base" GHC.Generics (Generic1(..))

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import Lift.DataDeps hiding (thd)

import Debug.Trace

thd :: (a, b, c) -> c
thd (a, b, c) = c

extractOcc :: Name -> String
extractOcc (Name (OccName str) _) = str

data family BaseBi from to :: * -> *

class RecursiveBi from to where
  embedBi :: BaseBi from to to -> from
  projectBi :: from -> BaseBi from to to

convertName :: Int -> Name -> Q Name
convertName idx name = pure $ mkName $ extractOcc name ++ suffix
  where
    suffix = if isInfix name then replicate (idx + 1) '$' else "FB" ++ show idx
    isInfix = all isSymbol . extractOcc

convertCon :: Int -> Con -> Q Con
convertCon idx con =
  case con of
    NormalC name types -> NormalC <$> (convertName idx name) <*> pure types
    RecC name types -> RecC <$> (convertName idx name) <*> pure types
    InfixC lt name rt -> InfixC <$> pure lt <*> (convertName idx name) <*> pure rt
    GadtC names types finalType -> GadtC <$> (traverse (convertName idx) names) <*> pure types <*> pure finalType
    RecGadtC names types finalType -> RecGadtC <$> (traverse (convertName idx) names) <*> pure types <*> pure finalType
    _ -> pure con

mkMatchBranch :: Bool -> (Con, Con) -> Q (Pat, Exp)
mkMatchBranch project (NormalC origName _, NormalC changedName fields) = do
  args <- traverse (const $ newName "x") fields
  tupleHandlers <- traverse (flipTupleHandler project) (map snd fields)

  let patName = if project then origName else changedName
  let pat = ConP patName (map VarP args)

  let expName = if project then changedName else origName
  let tupleHandledArgs = zipWith ($) tupleHandlers $ map VarE args
  let exp = foldl AppE (ConE expName) tupleHandledArgs

  pure (pat, exp)
mkMatchBranch project (RecC origName _, RecC changedName namedFields) = do
  args <- traverse (\(name, _, _) -> newName $ extractOcc name) namedFields
  tupleHandlers <- traverse (flipTupleHandler project) (map thd namedFields)

  let patName = if project then origName else changedName
  let pat = ConP patName (map VarP args)

  let expName = if project then changedName else origName
  let tupleHandledArgs = zipWith ($) tupleHandlers $ map VarE args
  let exp = foldl AppE (ConE expName) tupleHandledArgs

  pure (pat, exp)
mkMatchBranch project (InfixC _ origName _, InfixC (_, lt) changedName (_, rt)) = do
  larg <- newName "x"
  lTupleHandler <- flipTupleHandler project lt
  rarg <- newName "y"
  rTupleHandler <- flipTupleHandler project rt

  let patName = if project then origName else changedName
  let pat = InfixP (VarP larg) patName (VarP rarg)

  let expName = if project then changedName else origName
  let exp = InfixE (Just $ lTupleHandler $ VarE larg) (ConE expName) (Just $ rTupleHandler $ VarE rarg)

  pure (pat, exp)
mkMatchBranch project (ForallC bndrs cxt origCon, ForallC _ _ newCon) = mkMatchBranch project (origCon, newCon)
mkMatchBranch project (GadtC _ _ _, _) = error "FoldableBi / BaseBi: GADTs not supported"
mkMatchBranch project (RecGadtC _ _ _, _) = error "FoldableBi / BaseBi: GADTs not supported"

data LTuple b a = LTuple a b
  deriving (Show, Eq, Functor, Generic1)

flipTupleHandler :: Bool -> Type -> Q (Exp -> Exp)
flipTupleHandler project typ =
  maybe (pure id) (fmap AppE) $ flipTupleHandler' project typ

flipTupleHandler' :: Bool -> Type -> Maybe (Q Exp)
flipTupleHandler' project (AppT ListT a)
  = appE [| map |] <$> flipTupleHandler' project a
flipTupleHandler' project (AppT (AppT (ConT conName) typ2) (VarT name))
  | conName == ''LTuple
  = if project
      then Just [| \(a, b) -> LTuple a b |]
      else Just [| \(LTuple a b) -> (a, b) |]
flipTupleHandler' _ _ = Nothing

deriveBaseBi :: [Name] -> (Name, Int, Name) -> Q [Dec]
deriveBaseBi derivs (super, idx, sub) = do
  aVar <- newName "a"

  TyConI dataD <- reify super

  let convertSub typ =
        case typ of
          ConT name | name == sub -> VarT aVar
          AppT (AppT (TupleT 2) (VarT name)) typ2 | name == aVar -> AppT (AppT (ConT ''LTuple) typ2) (VarT name)
          _ -> typ

  case dataD of
    DataD cxt name tyVarBndrs mkind cons deriv -> do
      holed <- transformBiM (convertCon idx) $ transformBi convertSub cons

      let extraDerivs = DerivClause Nothing $ map ConT derivs

      let toTyArg (PlainTV name) = VarT name
          toTyArg (KindedTV name kind) = SigT (VarT name) kind
      let tyArgs = [ConT super, ConT sub] ++ map toTyArg tyVarBndrs ++ [VarT aVar]

      let dataDeclaration = DataInstD cxt Nothing (foldl AppT (ConT ''BaseBi) tyArgs) mkind holed (deriv ++ [extraDerivs])

      embedBranches <- traverse (mkMatchBranch False) (cons `zip` holed)
      projectBranches <- traverse (mkMatchBranch True) (cons `zip` holed)

      let embedDefinition = FunD 'embedBi $ map (\(pat, exp) -> Clause [pat] (NormalB exp) []) embedBranches
      let projectDefinition = FunD 'projectBi $ map (\(pat, exp) -> Clause [pat] (NormalB exp) []) projectBranches

      let instanceD =
            InstanceD Nothing [] (foldl AppT (ConT ''RecursiveBi) [ConT super, ConT sub]) [embedDefinition, projectDefinition]

      pure [dataDeclaration, instanceD]
    TySynD name vars con -> pure []
    _ -> error $ "deriveBaseBi: Unsupported datatype: " ++ show dataD

deriveBaseBiFamily :: [Name] -> Name -> Q [Dec]
deriveBaseBiFamily derivs root = do
  dg <- depGraph root
  let scc = connectedTo root dg
  let allEdges = [(super, idx, sub) | (super, subs) <- foldMap dgToList scc, (idx, sub) <- zip [0..] subs]
  allInstances <- traverse (deriveBaseBi derivs) allEdges
  pure $ concat allInstances

nameUsedIn :: forall from. (DD.Data from, Biplate from Name) => from -> Name -> Bool
nameUsedIn exp name = name `elem` collectNames @from exp

collectNames :: forall from. (DD.Data from, Biplate from Name) => from -> [Name]
collectNames = fst . transformBiM @_ @from @Name (\x -> ([x], x))

data GTuple = GTuple { gTupleDecl :: Dec, gTupleTo :: Exp, gTupleFrom :: Exp }
  deriving (Show, Eq, Lift)

toGTuple :: [Name] -> Name -> Type -> Q (Maybe GTuple)
toGTuple derivs target outerType
  | (TupleT n, args) <- flattenApps outerType
  = do
    (typeName, dataName, gTupleDecl) <- mkGTuple derivs target args
    bindArgs <- sequence $ replicate n (newName "x")
    let gTupleTo = LamE [TupP (map VarP bindArgs)] $ foldr AppE (ConE dataName) (map VarE bindArgs)
    let gTupleFrom = LamE [ConP dataName (map VarP bindArgs)] $ TupE (map (Just . VarE) bindArgs)
    pure $ Just $ GTuple { gTupleDecl, gTupleTo, gTupleFrom }
  | otherwise
  = pure Nothing
  where
    flattenApps = fmap reverse . go
      where
        go (AppT func arg) =
          let (innerF, argList) = flattenApps func
          in
          (innerF, arg : argList)
        go type_ = (type_, [])

mkGTuple :: [Name] -> Name -> [Type] -> Q (Name, Name, Dec) -- ([(Name, Name)], [Type])
mkGTuple derivs target spec = do
  let collectVars :: Type -> [Name]
      collectVars typ = [name | VarT name <- universe typ]

  let oldVars :: [Name]
      oldVars = nub $ filter (/= target) $ concatMap collectVars spec

  newVars <- traverse (newName . extractOcc) oldVars

  holeVar <- newName "a"
  let varPairs = zip oldVars newVars ++ [(target, holeVar)]

  let replaceVar = transformBi @Type @Name $ \name -> fromMaybe name $ name `lookup` varPairs
  let replacedTypes = map replaceVar spec

  typeName <- newName "AuxGTuple"
  dataName <- newName "AuxGTuple"

  let bang typ = (Bang NoSourceUnpackedness NoSourceStrictness, typ)
  let definition =
        DataD []
          typeName
          (map (PlainTV . snd) varPairs)
          Nothing
          [NormalC dataName $ map bang replacedTypes]
          [DerivClause Nothing $ ConT <$> derivs]

  pure (typeName, dataName, definition)
