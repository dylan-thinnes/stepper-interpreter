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
import "base" Data.Char
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

extractOcc :: Name -> String
extractOcc (Name (OccName str) _) = str

data family BaseBi from to :: * -> *

class RecursiveBi from to where
  embedBi :: BaseBi from to to -> from
  projectBi :: from -> BaseBi from to to

convertName :: Int -> Name -> Q Name
convertName idx name = pure $ mkName $ extractOcc name ++ suffix
  where
    suffix = if isInfix name then replicate (idx + 1) '$' else "FB" ++ show idx
    isInfix = all isSymbol . extractOcc

convertCon :: Int -> Con -> Q Con
convertCon idx con =
  case con of
    NormalC name types -> NormalC <$> (convertName idx name) <*> pure types
    RecC name types -> RecC <$> (convertName idx name) <*> pure types
    InfixC lt name rt -> InfixC <$> pure lt <*> (convertName idx name) <*> pure rt
    GadtC names types finalType -> GadtC <$> (traverse (convertName idx) names) <*> pure types <*> pure finalType
    RecGadtC names types finalType -> RecGadtC <$> (traverse (convertName idx) names) <*> pure types <*> pure finalType
    _ -> pure con

mkMatchBranch :: Int -> Bool -> Con -> Q (Pat, Exp)
mkMatchBranch idx project (NormalC name fields) = do
  args <- traverse (const $ newName "x") fields

  patName <- if project then pure name else convertName idx name
  let pat = ConP patName (map VarP args)

  expName <- if project then convertName idx name else pure name
  let exp = foldl AppE (ConE expName) (map VarE args)

  pure (pat, exp)
mkMatchBranch idx project (RecC name namedFields) = do
  args <- traverse (\(name, _, _) -> newName $ extractOcc name) namedFields

  patName <- if project then pure name else convertName idx name
  let pat = ConP patName (map VarP args)

  expName <- if project then convertName idx name else pure name
  let exp = foldl AppE (ConE expName) (map VarE args)

  pure (pat, exp)
mkMatchBranch idx project (InfixC lt name rt) = do
  larg <- newName "x"
  rarg <- newName "y"

  patName <- if project then pure name else convertName idx name
  let pat = InfixP (VarP larg) patName (VarP rarg)

  expName <- if project then convertName idx name else pure name
  let exp = InfixE (Just $ VarE larg) (ConE expName) (Just $ VarE rarg)

  pure (pat, exp)
mkMatchBranch idx project (ForallC bndrs cxt con) = mkMatchBranch idx project con
mkMatchBranch idx project (GadtC _ _ _) = error "FoldableBi / BaseBi: GADTs not supported"
mkMatchBranch idx project (RecGadtC _ _ _) = error "FoldableBi / BaseBi: GADTs not supported"

deriveBaseBi :: [Name] -> (Name, Int, Name) -> Q [Dec]
deriveBaseBi derivs (super, idx, sub) = do
  aVar <- newName "a"

  TyConI dataD <- reify super

  let convertSub typ =
        case typ of
          ConT name | name == sub -> VarT aVar
          _ -> typ

  case dataD of
    DataD cxt name tyVarBndrs mkind cons deriv -> do
      holed <- transformBiM (convertCon idx) $ transformBi convertSub cons

      let extraDerivs = DerivClause Nothing $ map ConT derivs

      let toTyArg (PlainTV name) = VarT name
          toTyArg (KindedTV name kind) = SigT (VarT name) kind
      let tyArgs = [ConT super, ConT sub] ++ map toTyArg tyVarBndrs ++ [VarT aVar]

      let dataDeclaration = DataInstD cxt Nothing (foldl AppT (ConT ''BaseBi) tyArgs) mkind holed (deriv ++ [extraDerivs])

      embedBranches <- traverse (mkMatchBranch idx False) cons
      projectBranches <- traverse (mkMatchBranch idx True) cons

      let embedDefinition = FunD 'embedBi $ map (\(pat, exp) -> Clause [pat] (NormalB exp) []) embedBranches
      let projectDefinition = FunD 'projectBi $ map (\(pat, exp) -> Clause [pat] (NormalB exp) []) projectBranches

      let instanceD =
            InstanceD Nothing [] (foldl AppT (ConT ''RecursiveBi) [ConT super, ConT sub]) [embedDefinition, projectDefinition]

      pure [dataDeclaration, instanceD]
    TySynD name vars con -> pure []
    _ -> error $ "deriveBaseBi: Unsupported datatype: " ++ show dataD

deriveBaseBiFamily :: [Name] -> Name -> Q [Dec]
deriveBaseBiFamily derivs root = do
  dg <- depGraph root
  let scc = connectedTo root dg
  let allEdges = [(super, idx, sub) | (super, subs) <- foldMap dgToList scc, (idx, sub) <- zip [0..] subs]
  allInstances <- traverse (deriveBaseBi derivs) allEdges
  pure $ concat allInstances
