{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lift where

import "base" Control.Monad ((<=<), zipWithM)
import "base" Data.Bifunctor
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Identity
import "base" Data.Functor.Product
import "base" Foreign.ForeignPtr
import "base" GHC.Generics (Generic(..), Generic1(..))
import "base" Data.Data qualified as DD

import "data-fix" Data.Fix (Fix(..))

import "deriving-compat" Text.Show.Deriving

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "lens" Control.Lens qualified as L

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import Lift.Lift
import Lift.DeepHoled.Instances
import Lift.DeepHoled qualified as DH

--R.makeBaseFunctor ''Exp
R.makeBaseFunctor ''Pat

deriveShow1 ''PatF
--deriveShow1 ''ExpF
type ExpF = ExpFExp

deriving instance Show a => Show (PatF a)
deriving instance Generic1 PatF
type instance Key PatF = Key (Rep1 PatF)
instance Keyed PatF where
  mapWithKey g fa = to1 $ mapWithKey g (from1 fa)
instance Adjustable PatF where
  adjust g k fa = mapWithKey (\k' x -> if k == k' then g x else x) fa

type PatKey = [Key PatF]
type ExpKey = [Key ExpFExp]

modPatByKey :: PatKey -> (Pat -> Pat) -> Pat -> Pat
modPatByKey = adjustRecursive

modExpByKey :: ExpKey -> (Exp -> Exp) -> Exp -> Exp
modExpByKey = adjustRecursive

modPatByKeyA :: Applicative m => PatKey -> (Pat -> m Pat) -> Pat -> m Pat
modPatByKeyA = adjustRecursiveA

modExpByKeyA :: Applicative m => ExpKey -> (Exp -> m Exp) -> Exp -> m Exp
modExpByKeyA = adjustRecursiveA

modAnnExpByKeyA :: Applicative m => ExpKey -> (RecKey Exp -> m (RecKey Exp)) -> RecKey Exp -> m (RecKey Exp)
modAnnExpByKeyA = adjustRecursiveGA (\f k (Pair cann ffix) -> Pair cann (adjust f k ffix))

dekeyed :: Functor f => f (Key f, a) -> f a
dekeyed = fmap snd

projectK :: (R.Recursive t, Keyed (R.Base t)) => t -> R.Base t (Key (R.Base t), t)
projectK = keyed . R.project

embedK :: (R.Corecursive t, Keyed (R.Base t)) => R.Base t (Key (R.Base t), t) -> t
embedK = R.embed . dekeyed

adjustRecursive
  :: (R.Base t ~ f, Adjustable f, Traversable f, R.Corecursive t, R.Recursive t)
  => [Key (R.Base t)] -> (t -> t) -> t -> t
adjustRecursive keys f t = runIdentity $ adjustRecursiveA keys (Identity . f) t

adjustRecursiveA
  :: (R.Base t ~ f, Adjustable f, Traversable f, R.Corecursive t, R.Recursive t, Applicative m)
  => [Key (R.Base t)] -> (t -> m t) -> t -> m t
adjustRecursiveA keys f t = adjustRecursiveGA adjust keys f t

adjustRecursiveG
  :: (f ~ R.Base t, Traversable f, R.Corecursive t, R.Recursive t)
  => (forall a. (a -> a) -> k -> f a -> f a)
  -> [k]
  -> (t -> t)
  -> t -> t
adjustRecursiveG adjust keys f t = runIdentity $ adjustRecursiveGA adjust keys (Identity . f) t

adjustRecursiveGA
  :: (f ~ R.Base t, Traversable f, R.Corecursive t, R.Recursive t, Applicative m)
  => (forall a. (a -> a) -> k -> f a -> f a)
  -> [k]
  -> (t -> m t)
  -> t -> m t
adjustRecursiveGA = adjustRecursiveGGA id

adjustRecursiveGGA
  :: forall m t u f g k
   . (f ~ R.Base t, g ~ R.Base u, Traversable g, R.Corecursive u, R.Recursive t, Applicative m)
  => (forall a. f a -> g a)
  -> (forall a. (a -> a) -> k -> f a -> g a)
  -> [k]
  -> (t -> m u)
  -> t -> m u
adjustRecursiveGGA reshape adjust [] f t = f t
adjustRecursiveGGA reshape adjust (k:rest) f t =
  -- have to do these shenanigans because `adjust` can't change type inside container
  let modifyWithWitness :: (m u, t) -> (m u, t)
      modifyWithWitness (_, a) = (adjustRecursiveGGA reshape adjust rest f a, a)

      pureWithWitness :: t -> (m u, t)
      pureWithWitness a = (pure $ R.hoist reshape a, a)
  in
  fmap R.embed
    $ sequenceA
    $ fmap fst
    $ adjust modifyWithWitness k
    $ fmap pureWithWitness
    $ R.project t

  {-
class RecKeyable t where
  type RecKey t :: *
  type RecKeyF t (f :: (* -> *) -> * -> *) :: * -> *

type RecAnn t ann = Fix (RecKeyF t (Product (Const ann)))
type RecKeyed t = RecAnn t (RecKey t)

instance RecKeyable Exp where
  type RecKey Exp = [Key ExpFExp]
  type RecKeyF Exp f = f ExpFExp

instance RecKeyable Pat where
  type RecKey Pat = [Key PatF]
  type RecKeyF Pat f = f PatF
  -}

type Ann a f = Product (Const a) f
type With t a = Fix (WithF t a)
type WithF t a = Ann a (R.Base t)
type RecKey t = With t [Key (R.Base t)]

pattern With t a = Fix (WithF t a)
pattern WithF t a = Pair (Const a) t

annKeys :: (R.Recursive t, Keyed (R.Base t)) => t -> RecKey t
annKeys exp = R.ana go ([], exp)
  where
    go (prekeys, exp) = Pair (Const prekeys) (first (\x -> prekeys ++ [x]) <$> projectK exp)

annOne :: a -> f (Fix (Ann a f)) -> Fix (Ann a f)
annOne a f = Fix (Pair (Const a) f)

type ExpWithKey = With Exp ExpKey

deann :: (R.Corecursive t, f ~ R.Base t) => Fix (Ann a f) -> t
deann = R.hoist (\(Pair _ tf) -> tf)

deannWrapped :: R.Corecursive t => R.Base t (With t a) -> t
deannWrapped = R.embed . fmap deann

toKeyPair :: Fix (Ann a f) -> (a, f (Fix (Ann a f)))
toKeyPair (Fix (Pair (Const key) expf)) = (key, expf)

fromKeyPair :: a -> f (Fix (Ann a f)) -> Fix (Ann a f)
fromKeyPair key expf = (Fix (Pair (Const key) expf))

toKeyPairDeann :: R.Corecursive t => RecKey t -> ([Key (R.Base t)], t)
toKeyPairDeann ann =
  let (key, expf) = toKeyPair ann
  in
  (key, R.embed $ fmap deann expf)

transformAllNames :: (DD.Data from, Biplate from Name) => (Name -> Name) -> from -> from
transformAllNames = transformBi

replaceName :: (DD.Data from, Biplate from Name) => Name -> Name -> from -> from
replaceName from to = transformAllNames (\name -> if name == from then to else name)

replaceName' :: (DD.Data from, Biplate from Exp) => Name -> Exp -> from -> from
replaceName' from to = transformBi (\name -> if name == VarE from then to else name)

--deriving instance DD.Data a => DD.Data (ExpF a)
--deriving instance DD.Data a => DD.Data (PatF a)

  {-
data T a = T0 Int (Int, a) (U [a]) (T a) | T1 a
  deriving (Functor, Generic1)
data U a = U0 (T a) | U1 a
  deriving (Functor, Generic1)

data Mk3 a b c = Mk3 a b c
  deriving (Generic1)

data V a = V0 (a, a)
  deriving (Show, Functor)
  -}

type instance R.Base Exp = DH.RecursiveF Exp
instance R.Recursive Exp where
  project = DH.project
instance R.Corecursive Exp where
  embed = DH.embed
