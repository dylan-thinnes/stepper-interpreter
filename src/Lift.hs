{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module Lift where

import "base" Foreign.ForeignPtr
import "base" GHC.Generics (Generic1(..))

import "deriving-compat" Text.Show.Deriving

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

instance Lift Bytes where
    lift _ = error "Cannot lift Bytes."
    liftTyped _ = error "Cannot lift Bytes."

deriving instance Lift AnnTarget
deriving instance Lift RuleBndr
deriving instance Lift InjectivityAnn
deriving instance Lift Phases
deriving instance Lift FamilyResultSig
deriving instance Lift RuleMatch
deriving instance Lift Inline
deriving instance Lift FixityDirection
deriving instance Lift Safety
deriving instance Lift Callconv
deriving instance Lift SourceStrictness
deriving instance Lift SourceUnpackedness
deriving instance Lift PkgName
deriving instance Lift NameSpace
deriving instance Lift PatSynDir
deriving instance Lift PatSynArgs
deriving instance Lift DerivStrategy
deriving instance Lift Role
deriving instance Lift TypeFamilyHead
deriving instance Lift TySynEqn
deriving instance Lift Pragma
deriving instance Lift Fixity
deriving instance Lift Foreign
deriving instance Lift Overlap
deriving instance Lift FunDep
deriving instance Lift Bang
deriving instance Lift ModName
deriving instance Lift DerivClause
deriving instance Lift Con
deriving instance Lift Clause
deriving instance Lift Body
deriving instance Lift TyLit
deriving instance Lift TyVarBndr
deriving instance Lift NameFlavour
deriving instance Lift OccName
deriving instance Lift Range
deriving instance Lift Stmt
deriving instance Lift Dec
deriving instance Lift Guard
deriving instance Lift Match
deriving instance Lift Pat
deriving instance Lift Type
deriving instance Lift Lit
deriving instance Lift Name
deriving instance Lift Exp

R.makeBaseFunctor ''Exp
R.makeBaseFunctor ''Pat

deriveShow1 ''ExpF
deriveShow1 ''PatF

deriving instance Show a => Show (PatF a)
deriving instance Generic1 PatF
type instance Key PatF = Key (Rep1 PatF)
instance Keyed PatF where
  mapWithKey g fa = to1 $ mapWithKey g (from1 fa)
instance Adjustable PatF where
  adjust g k fa = mapWithKey (\k' x -> if k == k' then g x else x) fa

deriving instance Show a => Show (ExpF a)
deriving instance Generic1 ExpF
type instance Key ExpF = Key (Rep1 ExpF)
instance Keyed ExpF where
  mapWithKey g fa = to1 $ mapWithKey g (from1 fa)
instance Adjustable ExpF where
  adjust g k fa = mapWithKey (\k' x -> if k == k' then g x else x) fa

type PatKey = [Key PatF]
type ExpKey = [Key ExpF]

modPatByKey :: (Pat -> Pat) -> PatKey -> Pat -> Pat
modPatByKey = adjustRecursive

modExpByKey :: (Exp -> Exp) -> ExpKey -> Exp -> Exp
modExpByKey = adjustRecursive

dekeyed :: Functor f => f (Key f, a) -> f a
dekeyed = fmap snd

projectK :: (R.Recursive t, Keyed (R.Base t)) => t -> R.Base t (Key (R.Base t), t)
projectK = keyed . R.project

embedK :: (R.Corecursive t, Keyed (R.Base t)) => R.Base t (Key (R.Base t), t) -> t
embedK = R.embed . dekeyed

adjustRecursive
  :: (Adjustable (R.Base t), R.Corecursive t, R.Recursive t)
  => (t -> t) -> [Key (R.Base t)] -> t -> t
adjustRecursive f [] t = f t
adjustRecursive f (k:rest) t = R.embed $ adjust (adjustRecursive f rest) k $ R.project t

adjustRecursiveG
  :: (R.Corecursive t, R.Recursive t)
  => (t -> t)
  -> (forall a. (a -> a) -> k -> R.Base t a -> R.Base t a)
  -> [k] -> t -> t
adjustRecursiveG f adjust [] t = f t
adjustRecursiveG f adjust (k:rest) t = R.embed $ adjust (adjustRecursiveG f adjust rest) k $ R.project t
