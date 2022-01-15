{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
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

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import Lift.DataDeps hiding (thd)

import Debug.Trace

thd :: (a, b, c) -> c
thd (a, b, c) = c

(<&>) = flip (<$>)

extractOcc :: Name -> String
extractOcc (Name (OccName str) _) = str

data family BaseBi from to :: * -> *

class RecursiveBi from to where
  embedBi :: BaseBi from to to -> from
  projectBi :: from -> BaseBi from to to

convertName :: (Int, Name) -> Name -> Q Name
convertName (idx, sub) name = pure $ mkName $ extractOcc name ++ suffix
  where
    suffix = if isInfix name then replicate (idx + 1) '$' else "FB" ++ extractOcc sub
    isInfix = all isSymbol . extractOcc

convertCon :: (Int, Name) -> Con -> Q Con
convertCon idxSub con =
  case con of
    NormalC name types -> NormalC <$> (convertName idxSub name) <*> pure types
    RecC name types -> RecC <$> (convertName idxSub name) <*> pure types
    InfixC lt name rt -> InfixC <$> pure lt <*> (convertName idxSub name) <*> pure rt
    GadtC names types finalType -> GadtC <$> (traverse (convertName idxSub) names) <*> pure types <*> pure finalType
    RecGadtC names types finalType -> RecGadtC <$> (traverse (convertName idxSub) names) <*> pure types <*> pure finalType
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
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1)

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
      holed <-
        transformBiM (convertCon (idx, sub))
          . transformBi convertSub
            =<< transformBiM (resolveTypeSynonym [''String, sub]) cons

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

resolveTypeSynonym :: [Name] -> Type -> Q Type
resolveTypeSynonym disallowed type_
  | (ConT funcName) <- func
  , funcName `notElem` disallowed
  = reify funcName <&>
    \case
      TyConI (TySynD name vars synonymType) ->
        let (actualArgs, additionalArgs) = splitAt (length vars) args
            varNames = map unTyVarBndr vars
            namesToActuals = zip varNames actualArgs
            replaceName =
              \case
                VarT name | Just actual <- lookup name namesToActuals -> actual
                other -> other
            newTyp = transformBi replaceName synonymType
        in
        foldr AppT newTyp additionalArgs
      _ -> type_
  | otherwise
  = pure type_
  where
    (func, args) = flattenAppTs type_
    unTyVarBndr (PlainTV name) = name
    unTyVarBndr (KindedTV name kind) = name

deriveBaseBiFamily :: [Name] -> Name -> Q [Dec]
deriveBaseBiFamily derivs root = do
  dg <- depGraph root
  let scc = connectedTo root dg
  let allEdges = [(super, idx, sub) | (super, subs) <- foldMap dgToList scc, (idx, sub) <- zip [0..] subs]
  allInstances <- traverse (deriveBaseBi derivs) allEdges
  pure $ concat allInstances

flattenAppTs :: Type -> (Type, [Type])
flattenAppTs = fmap reverse . go
  where
    go (AppT func arg) = (arg :) <$> go func
    go type_ = (type_, [])

data BiKey from to where
  BKNil :: BiKey a a
  (:::) ::
    ( BaseBi to newTo ~ base, Rep1 base ~ rep
    , Traversable base, Generic1 base
    , Keyed rep, Eq (Key rep), Show (Key rep)
    , RecursiveBi to newTo
    ) => BiKey from to -> Key rep -> BiKey from newTo

useRepKey :: forall m f a key. (Applicative m, Traversable f, Generic1 f, Keyed (Rep1 f), Key (Rep1 f) ~ key, Eq key) => key -> (a -> m a) -> f a -> m (f a)
useRepKey targetKey mod froma = sequenceA $ to1 $ mapWithKey mod' $ from1 froma
  where
    mod' :: key -> a -> m a
    mod' key a
      | key == targetKey = mod a
      | otherwise = pure a

adjustBiKey :: forall from to m. Applicative m => BiKey from to -> (to -> m to) -> from -> m from
adjustBiKey BKNil handler = handler
adjustBiKey (rest ::: (head :: Key (Rep1 (BaseBi b to)))) handler =
  adjustBiKey rest $ fmap embedBi . useRepKey head handler . projectBi @b @to

instance Show (BiKey a b) where
  show BKNil = "[]"
  show (head ::: tail) = show head ++ " ::: " ++ show tail

data BiKeyed from to where
  BKLast :: a -> BiKeyed a a
  (::::) :: BaseBi a b (Key (Rep1 (BaseBi a b)), BiKeyed b c) -> BiKeyed a c


