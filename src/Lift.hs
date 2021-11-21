{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

import "base" Control.Monad ((<=<))
import "base" Data.Bifunctor
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Identity
import "base" Data.Functor.Product
import "base" Foreign.ForeignPtr
import "base" GHC.Generics (Generic1(..))
import "base" Data.Data qualified as DD

import "data-fix" Data.Fix (Fix(..))

import "deriving-compat" Text.Show.Deriving

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import "uniplate" Data.Generics.Uniplate.Data

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
modPatByKey f key pat = runIdentity $ modPatByKeyA (Identity . f) key pat

modExpByKey :: (Exp -> Exp) -> ExpKey -> Exp -> Exp
modExpByKey f key exp = runIdentity $ modExpByKeyA (Identity . f) key exp

modPatByKeyA :: Applicative m => (Pat -> m Pat) -> PatKey -> Pat -> m Pat
modPatByKeyA = adjustRecursive

modExpByKeyA :: Applicative m => (Exp -> m Exp) -> ExpKey -> Exp -> m Exp
modExpByKeyA = adjustRecursive

dekeyed :: Functor f => f (Key f, a) -> f a
dekeyed = fmap snd

projectK :: (R.Recursive t, Keyed (R.Base t)) => t -> R.Base t (Key (R.Base t), t)
projectK = keyed . R.project

embedK :: (R.Corecursive t, Keyed (R.Base t)) => R.Base t (Key (R.Base t), t) -> t
embedK = R.embed . dekeyed

adjustRecursive
  :: (R.Base t ~ f, Adjustable f, Traversable f, R.Corecursive t, R.Recursive t, Applicative m)
  => (t -> m t) -> [Key (R.Base t)] -> t -> m t
adjustRecursive f [] t = f t
adjustRecursive f (k:rest) t =
  -- have to do these shenanigans because `adjust` can't change type inside container
  let modifyWithWitness (_, a) = (adjustRecursive f rest a, a)
      pureWithWitness a = (pure a, a)
  in
  fmap R.embed
    $ sequenceA
    $ fmap fst
    $ adjust modifyWithWitness k
    $ fmap pureWithWitness
    $ R.project t

adjustRecursiveG
  :: (R.Corecursive t, R.Recursive t)
  => (t -> t)
  -> (forall a. (a -> a) -> k -> R.Base t a -> R.Base t a)
  -> [k] -> t -> t
adjustRecursiveG f adjust [] t = f t
adjustRecursiveG f adjust (k:rest) t = R.embed $ adjust (adjustRecursiveG f adjust rest) k $ R.project t

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

class Mutplate from to where
  transformMutM :: Monad m => (to -> m to) -> from -> m from

instance Mutplate Name Name where
  transformMutM = id

deriving instance DD.Data a => DD.Data (ExpF a)
deriving instance DD.Data a => DD.Data (PatF a)

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
