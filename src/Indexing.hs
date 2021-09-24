{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Indexing where

import "base" Data.Void
import "base" GHC.Generics qualified as G

import "adjunctions" Data.Functor.Rep

import "distributive" Data.Distributive

import "lens" Control.Lens qualified as L

-- Indexing
class Recursive a where
  type Base a :: * -> *
  embed :: Base a a -> a
  project :: a -> Base a a

embedFix :: (Recursive a, Functor (Base a)) => Fix (Base a) -> a
embedFix (Fix ffix) = embed $ fmap embedFix ffix

projectFix :: (Recursive a, Functor (Base a)) => a -> Fix (Base a)
projectFix a = Fix $ fmap projectFix $ project a

data Fix f = Fix (f (Fix f))
type Idx f = [Rep f]

getRecRep
  :: (Recursive a, Representable (Base a))
  => a -> Idx (Base a) -> a
getRecRep a [] = a
getRecRep a (ii:rest) = getRecRep (index (project a) ii) rest

setRecRep
  :: (Recursive a, Representable (Base a), Eq (Rep (Base a)))
  => a -> Idx (Base a) -> a -> a
setRecRep super [] sub = sub
setRecRep super (ii:rest) sub = embed $ tabulate update
  where
    update rep
      | rep == ii = setRecRep (index (project super) rep) rest sub
      | otherwise = index (project super) rep

data Pair a b = Pair (Maybe (a, b))
  deriving (Show, Functor, G.Generic, G.Generic1)

--instance Indexable Maybe
instance Indexable Maybe
instance Indexable (Pair a)

instance Recursive [a] where
  type Base [a] = Pair a

  embed (Pair Nothing) = []
  embed (Pair (Just (a, rest))) = a : rest

  project [] = Pair Nothing
  project (a:rest) = Pair $ Just (a, rest)

fixGet
  :: (Recursive a, Functor (Base a), Indexable (Base a))
  => a -> [Index (Base a)] -> Maybe a
fixGet a [] = Just a
fixGet a (ii:rest) = do
  sub <- get (project a) ii
  fixGet sub rest

class Indexable f where
  type Index f :: *
  type Index f = Index' (G.Rep1 f)

  get :: f a -> Index f -> Maybe a
  default get :: (G.Generic1 f, Indexable' (G.Rep1 f), Index f ~ Index' (G.Rep1 f)) => f a -> Index f -> Maybe a
  get a idx = get' (G.from1 a) idx

class Indexable' f where
  type Index' f :: *
  get' :: f a -> Index' f -> Maybe a

instance
  (G.Generic1 f, G.Generic1 g, Indexable' (G.Rep1 f), Indexable' (G.Rep1 g)) =>
    Indexable' (f G.:+: g) where
  type Index' (f G.:+: g) = Either (Index' (G.Rep1 f)) (Index' (G.Rep1 g))
  get' (G.L1 fa) (Left idx) = get' (G.from1 fa) idx
  get' (G.R1 ga) (Right idx) = get' (G.from1 ga) idx
  get' _ _ = Nothing

instance
  (G.Generic1 f, G.Generic1 g, Indexable' (G.Rep1 f), Indexable' (G.Rep1 g)) =>
    Indexable' (f G.:*: g) where
  type Index' (f G.:*: g) = Either (Index' (G.Rep1 f)) (Index' (G.Rep1 g))
  get' (fa G.:*: ga) (Left idx) = get' (G.from1 fa) idx
  get' (fa G.:*: ga) (Right idx) = get' (G.from1 ga) idx

instance
  (G.Generic1 f, G.Generic1 g, Indexable' (G.Rep1 f), Indexable' (G.Rep1 g)) =>
    Indexable' (f G.:.: g) where
  type Index' (f G.:.: g) = (Index' (G.Rep1 f), Index' (G.Rep1 g))
  get' (G.Comp1 fga) (fidx, gidx) = do
    ga <- get' (G.from1 fga) fidx
    get' (G.from1 ga) gidx

instance Indexable' sub => Indexable' (G.M1 metaType meta sub) where
  type Index' (G.M1 metaType meta sub) = Index' sub
  get' = get' . G.unM1

instance Indexable' (G.K1 type_ c) where
  type Index' (G.K1 type_ c) = Void
  get' _ = absurd

instance Indexable' G.U1 where
  type Index' G.U1 = Void
  get' _ = absurd

instance Indexable' G.Par1 where
  type Index' G.Par1 = ()
  get' (G.Par1 x) () = Just x

instance (G.Generic1 f, Indexable' (G.Rep1 f)) => Indexable' (G.Rec1 f) where
  type Index' (G.Rec1 f) = Index' (G.Rep1 f)
  get' (G.Rec1 x) idx = get' (G.from1 x) idx
