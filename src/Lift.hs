{-# LANGUAGE DeriveDataTypeable #-}
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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lift where

import "base" Control.Monad ((<=<))
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

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import Lift.Lift
import Lift.BiKey

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

modPatByKeyA :: Applicative m => (Pat -> m Pat) -> PatKey -> Pat -> m Pat
modPatByKeyA = adjustRecursiveA

modExpByKeyA :: Applicative m => (Exp -> m Exp) -> ExpKey -> Exp -> m Exp
modExpByKeyA = adjustRecursiveA

modAnnExpByKeyA :: Applicative m => (Fix (RecKey Exp) -> m (Fix (RecKey Exp))) -> ExpKey -> Fix (RecKey Exp) -> m (Fix (RecKey Exp))
modAnnExpByKeyA f = adjustRecursiveGA f (\f k (Pair cann ffix) -> Pair cann (adjust f k ffix))

dekeyed :: Functor f => f (Key f, a) -> f a
dekeyed = fmap snd

projectK :: (R.Recursive t, Keyed (R.Base t)) => t -> R.Base t (Key (R.Base t), t)
projectK = keyed . R.project

embedK :: (R.Corecursive t, Keyed (R.Base t)) => R.Base t (Key (R.Base t), t) -> t
embedK = R.embed . dekeyed

adjustRecursive
  :: (R.Base t ~ f, Adjustable f, Traversable f, R.Corecursive t, R.Recursive t)
  => (t -> t) -> [Key (R.Base t)] -> t -> t
adjustRecursive f keys t = runIdentity $ adjustRecursiveA (Identity . f) keys t

adjustRecursiveA
  :: (R.Base t ~ f, Adjustable f, Traversable f, R.Corecursive t, R.Recursive t, Applicative m)
  => (t -> m t) -> [Key (R.Base t)] -> t -> m t
adjustRecursiveA f keys t = adjustRecursiveGA f adjust keys t

adjustRecursiveG
  :: (f ~ R.Base t, Traversable f, R.Corecursive t, R.Recursive t)
  => (t -> t)
  -> (forall a. (a -> a) -> k -> f a -> f a)
  -> [k] -> t -> t
adjustRecursiveG f adjust keys t = runIdentity $ adjustRecursiveGA (Identity . f) adjust keys t

adjustRecursiveGA
  :: (f ~ R.Base t, Traversable f, R.Corecursive t, R.Recursive t, Applicative m)
  => (t -> m t)
  -> (forall a. (a -> a) -> k -> f a -> f a)
  -> [k] -> t -> m t
adjustRecursiveGA f adjust [] t = f t
adjustRecursiveGA f adjust (k:rest) t =
  -- have to do these shenanigans because `adjust` can't change type inside container
  let modifyWithWitness (_, a) = (adjustRecursiveGA f adjust rest a, a)
      pureWithWitness a = (pure a, a)
  in
  fmap R.embed
    $ sequenceA
    $ fmap fst
    $ adjust modifyWithWitness k
    $ fmap pureWithWitness
    $ R.project t

adjustRecursiveGGA
  :: forall m t u f g k
   . (f ~ R.Base t, g ~ R.Base u, Traversable g, R.Corecursive u, R.Recursive t, Applicative m)
  => (t -> m u)
  -> (forall a. f a -> g a)
  -> (forall a. (a -> a) -> k -> f a -> g a)
  -> [k] -> t -> m u
adjustRecursiveGGA f reshape adjust [] t = f t
adjustRecursiveGGA f reshape adjust (k:rest) t =
  -- have to do these shenanigans because `adjust` can't change type inside container
  let modifyWithWitness :: (m u, t) -> (m u, t)
      modifyWithWitness (_, a) = (adjustRecursiveGGA f reshape adjust rest a, a)

      pureWithWitness :: t -> (m u, t)
      pureWithWitness a = (pure $ R.hoist reshape a, a)
  in
  fmap R.embed
    $ sequenceA
    $ fmap fst
    $ adjust modifyWithWitness k
    $ fmap pureWithWitness
    $ R.project t

listifyKey :: (a, b) -> ([a], b)
listifyKey = first (\x -> [x])

prependKey :: a -> ([a], b) -> ([a], b)
prependKey a = first (a :)

type Ann a f = Product (Const a) f
type RecKey t = Ann [Key (R.Base t)] (R.Base t)

annKeys :: (R.Recursive t, Keyed (R.Base t)) => t -> Fix (RecKey t)
annKeys exp = R.ana go ([], exp)
  where
    go (prekeys, exp) = Pair (Const prekeys) (first (\x -> prekeys ++ [x]) <$> projectK exp)

deann :: (R.Corecursive t, f ~ R.Base t) => Fix (Ann a f) -> t
deann = R.hoist (\(Pair _ tf) -> tf)

deannWrapped :: R.Corecursive t => R.Base t (Fix (RecKey t)) -> t
deannWrapped = R.embed . fmap deann

toKeyPair :: Fix (Ann a f) -> (a, f (Fix (Ann a f)))
toKeyPair (Fix (Pair (Const key) expf)) = (key, expf)

fromKeyPair :: a -> f (Fix (Ann a f)) -> Fix (Ann a f)
fromKeyPair key expf = (Fix (Pair (Const key) expf))

toKeyPairDeann :: R.Corecursive t => Fix (RecKey t) -> ([Key (R.Base t)], t)
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

deriving instance DD.Data a => DD.Data (ExpF a)
deriving instance DD.Data a => DD.Data (PatF a)

data T a = T0 Int (Int, a) (U a) (T a) | T1 a
  deriving (Generic1)
data U a = U0 (T a) | U1 a
  deriving (Generic1)

data Mk3 a b c = Mk3 a b c
  deriving (Generic1)

data V a = V0 (a, a)
  deriving (Show, Functor)

type X a b = (Int, [a], (b, a))

$(do
  a <- runQ (newName "a")
  b <- runQ (newName "b")
  let p = AppT (AppT (AppT (TupleT 3) (ConT ''Int)) (AppT ListT (VarT a))) (AppT (AppT (TupleT 2) (VarT b)) (VarT a))
  let (AppT (AppT (AppT _ t1) t2) t3) = p
  dec <- mkGTuple [''Show, ''Generic1] a [t1, t2, t3]
  pure [dec]
  )
