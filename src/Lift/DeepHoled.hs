{-# LANGUAGE PackageImports #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
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
module Lift.DeepHoled where

import "base" Control.Monad
import "base" Data.Char
import "base" Data.Data qualified as DD
import "base" Data.Foldable (toList)
import "base" Data.List
import "base" Data.Maybe (fromMaybe, fromJust)
import "base" GHC.Generics (Generic1(..))

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "lens" Control.Lens
import "lens" Control.Lens.TH

import "mtl" Control.Monad.Writer qualified as W
import "mtl" Control.Monad.State qualified as S

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import Lift.DataDeps
import Lift.Lift
import Utils

import Debug.Trace

$(makePrisms ''Dec)
$(makePrisms ''Type)
$(makePrisms ''Info)

type TypeSynonym = (Name, [TyVarBndr], Type)

toTypeSynonym :: Dec -> Maybe TypeSynonym
toTypeSynonym = preview _TySynD

fromTypeSynonym :: TypeSynonym -> Dec
fromTypeSynonym = review _TySynD

applySynonym :: TypeSynonym -> [Type] -> (Type, [Type])
applySynonym (name, vars, type_) args =
  let tyVarBndrName (PlainTV name) = name
      tyVarBndrName (KindedTV name kind) = name

      targetedVarNames = map tyVarBndrName vars `zip` args
      leftoverArgs = drop (length vars) args

      fillVar type_ =
        case type_ of
          VarT name
            | Just newDefinition <- lookup name targetedVarNames
            -> newDefinition
          _ -> type_

      newBody = transformBi fillVar type_
  in
  (newBody, leftoverArgs)

flattenAppTs :: Type -> (Type, [Type])
flattenAppTs = fmap reverse . go
  where
    go (AppT func arg) = (arg :) <$> go func
    go type_ = (type_, [])

unflattenAppTs :: Type -> [Type] -> Type
unflattenAppTs func args = foldl AppT func args

tryReplaceSynonym :: Type -> Q Type
tryReplaceSynonym type_ =
  case flattenAppTs type_ of
    (ConT funcName, args) | not $ null args -> do
      definition <- reify funcName
      case definition ^? _TyConI . _TySynD of
        (Just synonym) | length args == length (synonym ^. _2) ->
          let (newBody, leftoverArgs) = applySynonym synonym args
              newType = unflattenAppTs newBody leftoverArgs
          in
          replaceAnySynonyms newType
        _ -> pure type_
    _ -> pure type_

replaceAnySynonyms :: Type -> Q Type
replaceAnySynonyms = transformBiM tryReplaceSynonym

datatypeArity :: Name -> Q (Maybe Int)
datatypeArity name = do
  info <- reify name
  pure $ case info of
    TyConI (DataD _ _ tyvars _ _ _) -> Just $ length tyvars
    TyConI (NewtypeD _ _ tyvars _ _ _) -> Just $ length tyvars
    TyConI (TySynD _ tyvars _) -> Just $ length tyvars

type IdentifierMT k m = S.StateT ([(k, Int)], Int) m

newIdentifierBy :: (Monad m, Eq k) => k -> IdentifierMT k m (Int, Bool)
newIdentifierBy key = do
  (existing, identifier) <- S.get
  case lookup key existing of
    Just existingIdentifier -> pure (existingIdentifier, False)
    Nothing -> do
      S.put ((key, identifier) : existing, succ identifier)
      pure (identifier, True)

newIdentifier :: (Monad m) => IdentifierMT k m Int
newIdentifier = _2 <<%= succ

runIdentifierMT :: Monad m => IdentifierMT k m a -> m a
runIdentifierMT ma = S.evalStateT ma ([], 0)

runIdentifierM :: IdentifierMT k Identity a -> a
runIdentifierM = runIdentity . runIdentifierMT

class Recursive datatype where
  type RecursiveF datatype :: * -> *
  project :: datatype -> RecursiveF datatype Exp
  embed :: RecursiveF datatype Exp -> datatype

replaceTyVar :: Name -> Name -> Type -> Type
replaceTyVar target replacement = transformBi $ \type_ ->
  case type_ of
    VarT varName | varName == target -> VarT replacement
    _ -> type_

newtype GenericKey f = GenericKey { unGenericKey :: Key (Rep1 f) }
deriving instance Eq (Key (Rep1 f)) => Eq (GenericKey f)
deriving instance Show (Key (Rep1 f)) => Show (GenericKey f)

baseFunctorFamily :: Name -> Q [Dec]
baseFunctorFamily target = runIdentifierMT $ do
  let derivedClasses = [''Functor, ''Foldable, ''Traversable, ''Generic1]
  let derivedClasses1 = [''Show, ''Eq]

  let suffixName name = mkName $ rawName name ++ "F" ++ rawName target
  let unsuffixName name = mkName $ reverse $ drop (length ("F" ++ rawName target)) $ reverse $ rawName name

  mGraph <- S.lift $ connectedTo target <$> depGraphs [target]
  let graph = map (\(name, deps) -> (rawName name, deps)) $ dgToList $ fromJust mGraph

  let isNode name = rawName name `elem` map fst graph

  let replaceOtherGraphNodes :: Name -> Type -> IdentifierMT [Type] Q Type
      replaceOtherGraphNodes newTyVar = S.lift . transformBiM go
        where
        go type_ =
          case flattenAppTs type_ of
            (ConT nodeName, args)
              | nodeName == target -> pure $ unflattenAppTs (VarT newTyVar) args
              | isNode nodeName -> do
                  mArity <- datatypeArity nodeName
                  case mArity of
                    Just arity ->
                      let (preargs, postargs) = splitAt arity args
                          args' = preargs ++ [VarT newTyVar] ++ postargs
                      in
                      pure $ unflattenAppTs (ConT (suffixName nodeName)) args'
                    Nothing -> pure type_
            _ -> pure type_

  let replaceBadTuples :: Name -> Type -> W.WriterT [([Type], Dec)] (IdentifierMT [Type] Q) Type
      replaceBadTuples newTyVar = transformBiM go
        where
          mkSpecialTuple :: Name -> Name -> Name -> [Type] -> Dec
          mkSpecialTuple dataName conName varName types =
            let bang = Bang NoSourceUnpackedness NoSourceStrictness
                con = NormalC conName $ map (bang,) types
            in
            DataD [] dataName [PlainTV varName] Nothing [con] []

          lift :: Monoid w => Q a -> W.WriterT w (IdentifierMT [Type] Q) a
          lift = W.lift . S.lift

          go :: Type -> W.WriterT [([Type], Dec)] (IdentifierMT [Type] Q) Type
          go type_ =
            case flattenAppTs type_ of
              (TupleT n, args) | length args == n -> do
                replacedArgs <- traverse (S.lift . replaceOtherGraphNodes newTyVar) args
                let anyArgsRecursive = or [newTyVar == varName | VarT varName <- universeBi replacedArgs]
                if anyArgsRecursive
                  then do
                    (identifier, isNovel) <- W.lift $ newIdentifierBy $ replaceTyVar newTyVar (mkName "xxx") <$> args
                    let specialTupleDataName = mkName $ "SpecialTuple" ++ show n ++ "_" ++ show identifier
                    let specialTupleConName = mkName $ "ST" ++ show n ++ "_" ++ show identifier
                    let specialTupleTyVar = mkName "a"
                    let tupleArgs = replaceTyVar newTyVar specialTupleTyVar <$> replacedArgs
                    let specialTuple = mkSpecialTuple specialTupleDataName specialTupleConName specialTupleTyVar tupleArgs
                    if isNovel then W.tell [(args, specialTuple)] else pure ()
                    pure $ AppT (ConT specialTupleDataName) (VarT newTyVar)
                  else pure type_
              _ -> pure type_

  newDecss <- forM (graph `zip` [0..]) $ \((name, dependencies), ii) -> do
    info <- S.lift $ reify $ mkName name
    case info of
      TyConI (NewtypeD cxt name tyvars kind constructor derivations) -> do
        -- New name
        let name' = suffixName name

        -- New type variables
        newTyVar <- S.lift $ newName "a"
        let tyvars' = tyvars ++ [PlainTV newTyVar]

        -- New constructors
        constructor' <-
          constructor &
            overConNames %~ suffixName &
            overConTypes %%~ replaceOtherGraphNodes newTyVar

        pure [Left $ NewtypeD cxt name' tyvars' kind constructor' derivations]
      TyConI (TySynD name tyvars subtype) ->
        let name' = suffixName name
        in
        case flattenAppTs subtype of
          (TupleT _, origTupleTypes) -> do
            newTyVar <- S.lift $ newName "a"
            let tyvars' = tyvars ++ [PlainTV newTyVar]

            subtype' <- replaceOtherGraphNodes newTyVar subtype

            let (TupleT n, args) = flattenAppTs subtype'
                bang = Bang NoSourceUnpackedness NoSourceStrictness
                constructor = NormalC name' $ map (bang,) args
                dataDec = DataD [] name' tyvars' Nothing [constructor] []

            pure [Right (origTupleTypes, dataDec)]
          -- _ -> pure [Left $ TySynD name' tyvars' subtype']
          _ -> error "baseFunctorFamily: Does not support non-tuple type synonyms"
      TyConI (DataD cxt name tyvars mkind constructors deriveClauses) -> do
        -- New name
        let name' = suffixName name

        -- New type variables
        newTyVar <- S.lift $ newName "a"
        let tyvars' = tyvars ++ [PlainTV newTyVar]

        -- New constructors
        (constructors', specialTuples) <-
          W.runWriterT $
            constructors &
              traverse . overConTypes %%~ replaceBadTuples newTyVar
        constructors'' <-
          constructors' &
            traverse . overConNames %~ suffixName &
            traverse . overConTypes %%~ replaceOtherGraphNodes newTyVar
        let specialTuples' = map Right specialTuples

        pure $ Left (DataD cxt name' tyvars' mkind constructors'' deriveClauses) : specialTuples'
      _ -> pure []

  let newDecsWithSpecial = concat newDecss
      newDecs = map (either id snd) newDecsWithSpecial

  let decName (DataD _ name _ _ _ _) = [name]
      decName (NewtypeD _ name _ _ _ _) = [name]
      decName _ = []

  let decNames = concatMap decName newDecs

  deriveClassesDecsss <- S.lift $ forM decNames $ \name -> do
    forM derivedClasses $ \class_ ->
      [d| deriving instance $(conT class_) $(conT name) |]

  deriveClasses1Decsss <- S.lift $ forM decNames $ \name -> do
    forM derivedClasses1 $ \class_ -> do
      var <- newName "a"
      [d| deriving instance ($(conT class_ `appT` varT var)) => $(conT class_) $(conT name `appT` varT var) |]

  deriveKeys <- S.lift $ forM decNames $ \name ->
    let name' = conT name
    in
    [d|
      type instance Key $(name') = GenericKey (Rep1 $(name'))
      instance Keyed $(name') where
        mapWithKey g fa = to1 $ mapWithKey (g . GenericKey) (from1 fa)
      instance Adjustable $(name') where
        adjust g k fa = mapWithKey (\k' x -> if k == k' then g x else x) fa
    |]

  -- Return whether the type is recursive, and if so to what depth
  let isRecursive :: Type -> Q (Maybe Int)
      isRecursive type_ =
        let (func, args) = flattenAppTs type_
        in
        case (func, args) of
          (ConT name, args)
            | isNode $ unsuffixName name -> pure $ Just 0
            | take 12 (rawName name) == "SpecialTuple" -> pure $ Just 0
          (func, args) -> do
              isFunctor <-
                case func of
                  ConT funcConName -> do
                    info <- reify funcConName
                    case info of
                      TyConI (DataD _ _ tyvars _ _ _) | not (null tyvars) -> do
                        instances <- reifyInstances ''Functor [unflattenAppTs func (init args)]
                        if not $ null instances
                           then pure True
                           else pure False
                      _ -> pure False
                  ListT -> pure True
                  TupleT n -> pure True
                  _ -> pure False
              if isFunctor
                 then fmap succ <$> isRecursive (last args)
                 else pure Nothing

  deriveRecursive <- S.lift $ forM newDecsWithSpecial $ \dec -> do
    case dec of
      Right (origTupleTypes, tupleDec) ->
        case tupleDec of
          DataD cxt dataname tyvars mkind constructors deriveClauses -> do
            let nonrecType = unflattenAppTs (TupleT (length origTupleTypes)) origTupleTypes
            (projects, embeds) <- fmap unzip $ forM constructors $ \(NormalC conName bangTypes) -> do
              let types = map snd bangTypes
              project <- do
                expArgNames <- sequence (replicate (length types) (newName "x"))
                recursiveDepths <- forM types isRecursive
                let pat = TupP $ map VarP expArgNames
                let mkExpProject expArgName Nothing = varE expArgName
                    mkExpProject expArgName (Just n) = do
                      let fmapN 0 = [| id |]
                          fmapN n = [| fmap . $(fmapN (n - 1)) |]
                      (fmapN n `appE` [| project |]) `appE` varE expArgName
                projectedArgs <- sequence $ zipWith mkExpProject expArgNames recursiveDepths
                let exp = foldl AppE (ConE conName) projectedArgs
                pure (pat, exp)
              embed <- do
                expArgNames <- sequence (replicate (length types) (newName "x"))
                recursiveDepths <- forM types isRecursive
                let pat = ConP conName $ map VarP expArgNames
                let mkExpProject expArgName Nothing = varE expArgName
                    mkExpProject expArgName (Just n) = do
                      let fmapN 0 = [| id |]
                          fmapN n = [| fmap . $(fmapN (n - 1)) |]
                      (fmapN n `appE` [| embed |]) `appE` varE expArgName
                projectedArgs <- sequence $ zipWith mkExpProject expArgNames recursiveDepths
                let exp = TupE $ map Just projectedArgs
                pure (pat, exp)
              pure (project, embed)

            let mkClause (pat, exp) = Clause [pat] (NormalB exp) []
                embedDefinition = FunD (mkName "embed") $ map mkClause embeds
                projectDefinition = FunD (mkName "project") $ map mkClause projects

            typeInstanceDec <- [d| type instance RecursiveF $(pure nonrecType) = $(conT dataname) |]

            pure [InstanceD Nothing [] (ConT ''Recursive `AppT` nonrecType) (typeInstanceDec ++ [embedDefinition, projectDefinition])]
          _ -> error "baseFunctorFamily: Special tuple has unexpected declaration?"
      Left dataDec ->
        case dataDec of
          TySynD dataname tyvars type_ -> pure [] -- error "baseFunctorFamily: Doesn't support type synonyms"
          DataD cxt dataname tyvars mkind constructors deriveClauses -> do
            let nonrecType = ConT (unsuffixName dataname)
            (projects, embeds) <- fmap unzip $ forM constructors $ \(NormalC conName bangTypes) -> do
              let nonrecConName = unsuffixName conName
              let types = map snd bangTypes
              project <- do
                expArgNames <- sequence (replicate (length types) (newName "x"))
                recursiveDepths <- forM types isRecursive
                let pat = ConP nonrecConName $ map VarP expArgNames
                let mkExpProject expArgName Nothing = varE expArgName
                    mkExpProject expArgName (Just n) = do
                      let fmapN 0 = [| id |]
                          fmapN n = [| fmap . $(fmapN (n - 1)) |]
                      (fmapN n `appE` [| project |]) `appE` varE expArgName
                projectedArgs <- sequence $ zipWith mkExpProject expArgNames recursiveDepths
                let exp = foldl AppE (ConE conName) projectedArgs
                pure (pat, exp)
              embed <- do
                expArgNames <- sequence (replicate (length types) (newName "x"))
                recursiveDepths <- forM types isRecursive
                let pat = ConP conName $ map VarP expArgNames
                let mkExpProject expArgName Nothing = varE expArgName
                    mkExpProject expArgName (Just n) = do
                      let fmapN 0 = [| id |]
                          fmapN n = [| fmap . $(fmapN (n - 1)) |]
                      (fmapN n `appE` [| embed |]) `appE` varE expArgName
                projectedArgs <- sequence $ zipWith mkExpProject expArgNames recursiveDepths
                let exp = foldl AppE (ConE nonrecConName) projectedArgs
                pure (pat, exp)
              pure (project, embed)

            let mkClause (pat, exp) = Clause [pat] (NormalB exp) []
                embedDefinition = FunD (mkName "embed") $ map mkClause embeds
                projectDefinition = FunD (mkName "project") $ map mkClause projects

            typeInstanceDec <- [d| type instance RecursiveF $(pure nonrecType) = $(conT dataname) |]

            pure [InstanceD Nothing [] (ConT ''Recursive `AppT` nonrecType) (typeInstanceDec ++ [embedDefinition, projectDefinition])]
          _ -> pure []

  let concatcat = concat . concat
  pure $ newDecs ++ concatcat deriveClassesDecsss ++ concatcat deriveClasses1Decsss ++ concat deriveKeys ++ concat deriveRecursive
