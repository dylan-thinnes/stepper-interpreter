{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
module Lift.DataDeps where

import "base" Control.Monad (foldM)
import "base" GHC.Generics (Generic (..))

import "containers" Data.Graph qualified as G
import "containers" Data.Map qualified as M
import "containers" Data.Set qualified as S

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data qualified as B

import Debug.Trace

-- utils
snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd :: (a, b, c) -> c
thd (_, _, c) = c

deriving instance Lift NameSpace
deriving instance Lift PkgName
deriving instance Lift ModName
deriving instance Lift NameFlavour
deriving instance Lift OccName
deriving instance Lift Name

-- dependency graphs and their ops
type DepGraph = M.Map Name (S.Set Name)

dgToList :: DepGraph -> [(Name, [Name])]
dgToList = (fmap . fmap) S.toList . M.toList

dgFromList :: [(Name, [Name])] -> DepGraph
dgFromList = M.fromList . (fmap . fmap) S.fromList

dependents :: Name -> DepGraph -> [(Name, [Name])]
dependents dependency depGraph =
  let edges = map (\(n, ns) -> ((), n, ns)) $ dgToList depGraph
      (graph, lookupVertex, lookupName) = G.graphFromEdges edges
      Just dependencyV = lookupName dependency
  in do
    let vertices = G.reachable (G.transposeG graph) dependencyV
    let namesDepss = map lookupVertex vertices
    let depss = map snd3 namesDepss
    (_, name, deps) <- namesDepss
    pure (name, filter (`elem` depss) deps)

class Mutplate from to where
  transformMutM :: forall m. Monad m => (to -> m to) -> from -> m from

deriveMutplate :: Name -> [Name] -> Q [Dec]
deriveMutplate target roots = do
  depGraph <- depGraphs roots
  fName <- newName "f"
  let entryPoints = dependents target depGraph
      declareEntryPoint (entryPoint, dependencies) =
        let isCriticalDep name = name /= entryPoint && elem name (map fst entryPoints)
            criticalDeps = filter isCriticalDep dependencies
            qCompose lExp rExp = [e| $(lExp) <=< $(rExp) |]
            qChildrenBi dependency =
              [|
                transformBiM @_ @($(conT entryPoint)) @($(conT dependency))
                  (transformMutM @($(conT dependency)) @($(conT target)) @_
                    $(varE fName))
              |]
            body
              | entryPoint == target = [e| $(varE fName) |]
              | otherwise = foldr qCompose [e| pure |] (map qChildrenBi criticalDeps)
        in
        [d|
          instance Mutplate $(conT entryPoint) $(conT target) where
            transformMutM $(varP fName) = $(body)
        |]
  instances <- traverse declareEntryPoint entryPoints
  pure $ concat instances

-- creating depGraphs in TH from Name
depGraphs :: [Name] -> Q DepGraph
depGraphs names = M.unions <$> traverse depGraph names

depGraph :: Name -> Q DepGraph
depGraph topName = go topName M.empty
  where
  go :: Name -> DepGraph -> Q DepGraph
  go name graph = do
    mdeps <- lookupDepData name
    case mdeps of
      Nothing -> pure graph
      Just deps ->
        let graph' = M.insert name deps graph
            unseenDeps = filter (`M.notMember` graph') (S.toList deps)
            graph'' = foldM (flip go) graph' unseenDeps
        in
        graph''

lookupDepData :: Name -> Q (Maybe (S.Set Name))
lookupDepData name = do
  info <- reify name
  case info of
    TyConI (DataD cxt name tyVarBndrs kind constructors derivations) ->
      pure $ Just $ S.fromList $ do
        con <- constructors
        type_ <- typesFromCon con
        concreteTypes type_
    TyConI (NewtypeD cxt name tyVarBndrs kind constructor derivations) ->
      pure $ Just $ S.fromList $ do
        con <- [constructor]
        type_ <- typesFromCon con
        concreteTypes type_
    TyConI (TySynD name tyVarBndrs subtype) ->
      pure $ Just $ S.fromList $ concreteTypes subtype
    _ -> pure Nothing

typesFromCon :: Con -> [Type]
typesFromCon (NormalC _ bangTypes) = map snd bangTypes
typesFromCon (RecC _ varBangTypes) = map thd varBangTypes
typesFromCon (InfixC bangType1 _ bangType2) = map snd [bangType1, bangType2]
typesFromCon (ForallC _ _ con) = typesFromCon con
typesFromCon (GadtC _ bangTypes _) = map snd bangTypes
typesFromCon (RecGadtC _ varBangTypes _) = map thd varBangTypes

concreteTypes :: Type -> [Name]
concreteTypes type_ = do
  child <- B.universeBi @Type @Type type_
  case child of
    ConT name -> pure name
    InfixT _ name _ -> pure name
    UInfixT _ name _ -> pure name
    _ -> []
