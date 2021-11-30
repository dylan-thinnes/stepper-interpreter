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
import "base" GHC.Generics (Generic1(..))
import "base" Data.Data qualified as DD

import "containers" Data.Map qualified as M

import "data-fix" Data.Fix (Fix(..))

import "deriving-compat" Text.Show.Deriving

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import Debug.Trace

import Lift.DataDeps

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
deriving instance Lift DerivClause
deriving instance Lift Con
deriving instance Lift Clause
deriving instance Lift Body
deriving instance Lift TyLit
deriving instance Lift TyVarBndr
deriving instance Lift Range
deriving instance Lift Stmt
deriving instance Lift Dec
deriving instance Lift Guard
deriving instance Lift Match
deriving instance Lift Pat
deriving instance Lift Type
deriving instance Lift Lit
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

transformAllNames :: Mutplate from Name => (Name -> Name) -> from -> from
transformAllNames f = runIdentity . transformMutM (Identity . f)

replaceName :: Mutplate from Name => Name -> Name -> from -> from
replaceName from to = transformAllNames (\name -> if name == from then to else name)

instance Mutplate Name Name where
  transformMutM = id

deriving instance DD.Data a => DD.Data (ExpF a)
deriving instance DD.Data a => DD.Data (PatF a)

transformMut :: Mutplate from to => (to -> to) -> from -> from
transformMut f = runIdentity . transformMutM (Identity . f)

instance
  ( DD.Data a
  , DD.Data (f (Fix (Ann a f)))
  , Traversable f
  , Mutplate (f (Fix (Ann a f))) to
  ) => Mutplate (Fix (Ann a f)) to where
  transformMutM :: forall m. Monad m => (to -> m to) -> Fix (Ann a f) -> m (Fix (Ann a f))
  transformMutM f (Fix (Pair cmann expf)) =
    fmap (Fix . Pair cmann) $ transformMutM f =<< traverse (transformMutM f) expf
    where
      f' :: f (Fix (Ann a f)) -> m (f (Fix (Ann a f)))
      f' expf = transformMutM @(f _) @to f expf

instance DD.Data a => Mutplate (PatF a) Name where
  transformMutM f
    = transformBiM @_ @(PatF a) @Name (transformMutM f)
    <=< transformBiM @_ @(PatF a) @Exp (transformMutM f)
    <=< transformBiM @_ @(PatF a) @FieldPat (transformMutM f)

instance DD.Data a => Mutplate (ExpF a) Name where
  transformMutM f
    = transformBiM @_ @(ExpF a) @Name (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Guard (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Pat (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Type (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Stmt (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @FieldExp (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Match (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Range (transformMutM f)
    <=< transformBiM @_ @(ExpF a) @Dec (transformMutM f)

instance Mutplate Exp Name where
  transformMutM f
    = transformBiM @_ @Exp @Name (transformMutM f)
    <=< transformBiM @_ @Exp @Guard (transformMutM f)
    <=< transformBiM @_ @Exp @Pat (transformMutM f)
    <=< transformBiM @_ @Exp @Type (transformMutM f)
    <=< transformBiM @_ @Exp @Stmt (transformMutM f)
    <=< transformBiM @_ @Exp @FieldExp (transformMutM f)
    <=< transformBiM @_ @Exp @Match (transformMutM f)
    <=< transformBiM @_ @Exp @Range (transformMutM f)
    <=< transformBiM @_ @Exp @Dec (transformMutM f)

instance Mutplate Pat Name where
  transformMutM f
    = transformBiM @_ @Pat @Name (transformMutM f)
    <=< transformBiM @_ @Pat @Exp (transformMutM f)
    <=< transformBiM @_ @Pat @FieldPat (transformMutM f)

instance Mutplate FieldPat Name where
  transformMutM f
    = transformBiM @_ @FieldPat @Name (transformMutM f)
    <=< transformBiM @_ @FieldPat @Pat (transformMutM f)

instance Mutplate Match Name where
  transformMutM f
    = transformBiM @_ @Match @Pat (transformMutM f)
    <=< transformBiM @_ @Match @Body (transformMutM f)
    <=< transformBiM @_ @Match @Dec (transformMutM f)

instance Mutplate Body Name where
  transformMutM f
    = transformBiM @_ @Body @Exp (transformMutM f)
    <=< transformBiM @_ @Body @Guard (transformMutM f)

instance Mutplate Guard Name where
  transformMutM f
    = transformBiM @_ @Guard @Exp (transformMutM f)
    <=< transformBiM @_ @Guard @Stmt (transformMutM f)

instance Mutplate Dec Name where
  transformMutM f
    = transformBiM @_ @Dec @Name (transformMutM f)
    <=< transformBiM @_ @Dec @Pat (transformMutM f)
    <=< transformBiM @_ @Dec @Body (transformMutM f)
    <=< transformBiM @_ @Dec @Clause (transformMutM f)

instance Mutplate Range Name where
  transformMutM f
    = transformBiM @_ @Range @Exp (transformMutM f)

instance Mutplate FieldExp Name where
  transformMutM f
    = transformBiM @_ @FieldExp @Name (transformMutM f)
    <=< transformBiM @_ @FieldExp @Exp (transformMutM f)

instance Mutplate Stmt Name where
  transformMutM f
    = transformBiM @_ @Stmt @Pat (transformMutM f)
    <=< transformBiM @_ @Stmt @Exp (transformMutM f)
    <=< transformBiM @_ @Stmt @Dec (transformMutM f)

instance Mutplate Type Name where
  transformMutM f
    = transformBiM @_ @Type @Name (transformMutM f)

instance Mutplate Clause Name where
  transformMutM f
    = transformBiM @_ @Clause @Pat (transformMutM f)
    <=< transformBiM @_ @Clause @Body (transformMutM f)
    <=< transformBiM @_ @Clause @Dec (transformMutM f)

-- example of deriveMutplate
data X = X1 Int | X2 Char | X3 Y
  deriving (Show, DD.Data, DD.Typeable)
data Y = Y1 X X | Y2 Char | Y3 Y
  deriving (Show, DD.Data, DD.Typeable)
data Z = Z1 X Y
  deriving (Show, DD.Data, DD.Typeable)

ex = (Y1 (X3 (Y1 (X1 0) (X2 'a'))) (X3 (Y1 (X2 'b') (X3 (Y2 'c')))))

-- $(deriveMutplate ''Bool [''Z])
instance Mutplate Char Char where
  transformMutM f_0 = f_0
instance Mutplate Y Char where
  transformMutM f_0 =
    transformBiM @_ @Y @Char f_0
instance Mutplate Z Char where
  transformMutM f_0 =
    transformBiM @_ @Z @X (transformMutM f_0)
      <=< transformBiM @_ @Z @Y (transformMutM f_0)
instance Mutplate X Char where
  transformMutM f_0 =
    transformBiM @_ @X @Char f_0
