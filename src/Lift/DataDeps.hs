{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
module Lift.DataDeps where

import "base" Control.Monad (foldM)
import "base" Data.Foldable (toList)
import "base" Data.Maybe (mapMaybe, listToMaybe)
import "base" GHC.Generics (Generic (..))

import "array" Data.Array qualified as A

import "containers" Data.Graph qualified as G
import "containers" Data.Map qualified as M
import "containers" Data.Set qualified as S

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data qualified as B

import Lift.Lift

import Debug.Trace

-- utils
snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd :: (a, b, c) -> c
thd (_, _, c) = c

-- dependency graphs and their ops
type DepGraph = M.Map Name (S.Set Name)

dgToList :: DepGraph -> [(Name, [Name])]
dgToList = (fmap . fmap) S.toList . M.toList

dgFromList :: [(Name, [Name])] -> DepGraph
dgFromList = M.fromList . (fmap . fmap) S.fromList

restrict :: (Name -> Bool) -> DepGraph -> DepGraph
restrict pred = M.map (S.filter pred) . M.filterWithKey (\k a -> pred k)

dgToGraph :: DepGraph -> (G.Graph, G.Vertex -> (Name, [Name]), Name -> Maybe G.Vertex)
dgToGraph depGraph = (graph, deunit . vertexToName, nameToVertex)
  where
    (graph, vertexToName, nameToVertex) = G.graphFromEdges $ map unit $ dgToList depGraph
    unit (n, ns) = ((), n, ns)
    deunit ((), n, ns) = (n, ns)

dependents :: Name -> DepGraph -> DepGraph
dependents dependency depGraph =
  let (graph, vertexToName, nameToVertex) = dgToGraph depGraph
  in
  case nameToVertex dependency of
    Nothing -> M.empty
    Just name ->
      let reachableVertices = G.reachable (G.transposeG graph) name
          reachableNames = fst . vertexToName <$> reachableVertices
      in
      restrict (`elem` reachableNames) depGraph

connectedTo :: Name -> DepGraph -> Maybe DepGraph
connectedTo name dg = do
  let (graph, vertexToName, nameToVertex) = dgToGraph dg
  vertex <- nameToVertex name
  connectedTo <- listToMaybe $ filter (elem vertex) $ G.scc graph
  let connectedVertices = fst . vertexToName <$> toList connectedTo
  pure $ restrict (`elem` connectedVertices) dg

edges :: DepGraph -> [(Name, Name)]
edges dg = [(start, end) | (start, ends) <- dgToList dg, end <- ends]

-- creating depGraphs in TH from Name
depGraphs :: [Name] -> Q DepGraph
depGraphs names = M.unions <$> traverse depGraph names

depGraph :: Name -> Q DepGraph
depGraph = go M.empty
  where
  go :: DepGraph -> Name -> Q DepGraph
  go graph name = do
    mdeps <- lookupDepData name
    case mdeps of
      Nothing -> pure graph
      Just deps ->
        let graph' = M.insert name deps graph
            unseenDeps = filter (`M.notMember` graph') (S.toList deps)
            graph'' = foldM go graph' unseenDeps
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
