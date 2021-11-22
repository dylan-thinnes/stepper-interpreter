{-# LANGUAGE TemplateHaskell #-}
module NamingExperiment where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Lift

LetE [ValD (VarP letXPat) _ _] (VarE letXExp) = $(lift =<< [| let x = x in x |])
(UnboundVarE bareXExp) = $(lift =<< [| x |])

occ :: Name -> OccName
occ (Name occName _) = occName

flavour :: Name -> NameFlavour
flavour (Name _ flavour) = flavour
