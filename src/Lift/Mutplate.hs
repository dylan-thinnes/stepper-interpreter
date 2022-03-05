{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Lift.Mutplate where

import Language.Haskell.TH
import Lift.DataDeps

class Mutplate from to where
  transformMutM :: forall m. Monad m => (to -> m to) -> from -> m from

deriveMutplate :: Name -> [Name] -> Q [Dec]
deriveMutplate target roots = do
  depGraph <- depGraphs roots
  fName <- newName "f"
  let entryPoints = dgToList $ dependents target depGraph
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

