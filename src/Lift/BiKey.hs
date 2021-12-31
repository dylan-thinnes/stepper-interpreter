{-# LANGUAGE PackageImports #-}
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

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import Lift.DataDeps

import Debug.Trace

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

mkMatchBranch :: Int -> Bool -> Con -> Q (Pat, Exp)
mkMatchBranch idx project (NormalC name fields) = do
  args <- traverse (const $ newName "x") fields

  patName <- if project then pure name else convertName idx name
  let pat = ConP patName (map VarP args)

  expName <- if project then convertName idx name else pure name
  let exp = foldl AppE (ConE expName) (map VarE args)

  pure (pat, exp)
mkMatchBranch idx project (RecC name namedFields) = do
  args <- traverse (\(name, _, _) -> newName $ extractOcc name) namedFields

  patName <- if project then pure name else convertName idx name
  let pat = ConP patName (map VarP args)

  expName <- if project then convertName idx name else pure name
  let exp = foldl AppE (ConE expName) (map VarE args)

  pure (pat, exp)
mkMatchBranch idx project (InfixC lt name rt) = do
  larg <- newName "x"
  rarg <- newName "y"

  patName <- if project then pure name else convertName idx name
  let pat = InfixP (VarP larg) patName (VarP rarg)

  expName <- if project then convertName idx name else pure name
  let exp = InfixE (Just $ VarE larg) (ConE expName) (Just $ VarE rarg)

  pure (pat, exp)
mkMatchBranch idx project (ForallC bndrs cxt con) = mkMatchBranch idx project con
mkMatchBranch idx project (GadtC _ _ _) = error "FoldableBi / BaseBi: GADTs not supported"
mkMatchBranch idx project (RecGadtC _ _ _) = error "FoldableBi / BaseBi: GADTs not supported"

deriveBaseBi :: [Name] -> (Name, Int, Name) -> Q [Dec]
deriveBaseBi derivs (super, idx, sub) = do
  aVar <- newName "a"

  TyConI dataD <- reify super

  let convertSub typ =
        case typ of
          ConT name | name == sub -> VarT aVar
          _ -> typ

  case dataD of
    DataD cxt name tyVarBndrs mkind cons deriv -> do
      holed <- transformBiM (convertCon idx) $ transformBi convertSub cons

      let extraDerivs = DerivClause Nothing $ map ConT derivs

      let toTyArg (PlainTV name) = VarT name
          toTyArg (KindedTV name kind) = SigT (VarT name) kind
      let tyArgs = [ConT super, ConT sub] ++ map toTyArg tyVarBndrs ++ [VarT aVar]

      let dataDeclaration = DataInstD cxt Nothing (foldl AppT (ConT ''BaseBi) tyArgs) mkind holed (deriv ++ [extraDerivs])

      embedBranches <- traverse (mkMatchBranch idx False) cons
      projectBranches <- traverse (mkMatchBranch idx True) cons

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
