{-# LANGUAGE PackageImports #-}
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
import "base" Data.Maybe (fromMaybe)
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
          in
          replaceAnySynonyms (unflattenAppTs newBody leftoverArgs)
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

type IdentifierMT m = S.StateT Int m

newIdentifier :: Monad m => IdentifierMT m Int
newIdentifier = do
  identifier <- S.get
  S.modify succ
  pure identifier

runIdentifierMT :: Monad m => IdentifierMT m a -> m a
runIdentifierMT ma = S.evalStateT ma 0

baseFunctorFamily :: Name -> Q [Dec]
baseFunctorFamily target = runIdentifierMT $ do
  let derivedClasses = [''Functor, ''Foldable, ''Traversable, ''Generic1]

  let suffixName name = mkName $ rawName name ++ "F" ++ rawName target
  graph <- S.lift $ dgToList . maybe undefined id . connectedTo target <$> depGraphs [target]

  let isNode name = name `elem` map fst graph
  let replaceOtherGraphNodes :: Name -> Type -> IdentifierMT Q Type
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

  let replaceBadTuples :: Name -> Type -> W.WriterT [Dec] (IdentifierMT Q) Type
      replaceBadTuples newTyVar = transformBiM go
        where
          mkSpecialTuple :: Name -> Name -> Name -> [Type] -> Dec
          mkSpecialTuple dataName conName varName types =
            let bang = Bang NoSourceUnpackedness NoSourceStrictness
                con = NormalC conName $ map (bang,) types
                deriveClause = DerivClause Nothing $ map ConT derivedClasses
            in
            DataD [] dataName [PlainTV varName] Nothing [con] [deriveClause]

          lift :: Monoid w => Q a -> W.WriterT w (IdentifierMT Q) a
          lift = W.lift . S.lift

          go :: Type -> W.WriterT [Dec] (IdentifierMT Q) Type
          go type_ =
            case flattenAppTs type_ of
              (TupleT n, args)
                | length args == n
                , or [newTyVar == varName | VarT varName <- universeBi type_] -> do
                  identifier <- W.lift newIdentifier
                  specialTupleDataName <- lift $ newName $ "SpecialTuple" ++ show n ++ "_" ++ show identifier
                  specialTupleConName <- lift $ newName $ "ST" ++ show n ++ "_" ++ show identifier
                  specialTupleTyVar <- lift $ newName "a"
                  let tupleArgs = flip transformBi args $ \type_ ->
                        case type_ of
                          VarT varName | varName == newTyVar -> VarT specialTupleTyVar
                          _ -> type_
                  W.tell [mkSpecialTuple specialTupleDataName specialTupleConName specialTupleTyVar tupleArgs]
                  pure $ AppT (ConT specialTupleDataName) (VarT newTyVar)
              _ -> pure type_

  newDecs <- forM (graph `zip` [0..]) $ \((name, dependencies), ii) -> do
    info <- S.lift $ reify name
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

        pure [NewtypeD cxt name' tyvars' kind constructor' derivations]
      TyConI (TySynD name tyvars subtype) -> do
        let name' = suffixName name

        newTyVar <- S.lift $ newName "a"
        let tyvars' = tyvars ++ [PlainTV newTyVar]

        subtype' <- replaceOtherGraphNodes newTyVar subtype

        pure [TySynD name' tyvars' subtype']
      TyConI (DataD cxt name tyvars mkind constructors deriveClauses) -> do
        -- New name
        let name' = suffixName name

        -- New type variables
        newTyVar <- S.lift $ newName "a"
        let tyvars' = tyvars ++ [PlainTV newTyVar]

        -- New constructors
        constructors' <-
          constructors &
            traverse . overConNames %~ suffixName &
            traverse . overConTypes %%~ replaceOtherGraphNodes newTyVar
        (constructors'', specialTuples) <-
          W.runWriterT $
            constructors' &
              traverse . overConTypes %%~ replaceBadTuples newTyVar

        pure $ [DataD cxt name' tyvars' mkind constructors'' deriveClauses] ++ specialTuples
      _ -> pure []

  deriveFunctors <- S.lift $ forM graph $ \(name, _) -> do
    info <- reify name
    if has (_TyConI . _TySynD) info
       then pure []
       else
         forM derivedClasses $ \class_ ->
           [d| deriving instance $(conT class_) $(conT $ suffixName name) |]

  deriveKeys <- S.lift $ forM graph $ \(name, _) -> do
    info <- reify name
    if has (_TyConI . _TySynD) info
       then pure []
       else
         let name' = conT $ suffixName name
         in
         [d| type instance Key $(name') = Key (Rep1 $(name')) |]

  pure $ concat $ newDecs ++ concat deriveFunctors ++ deriveKeys
