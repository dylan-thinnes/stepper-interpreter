{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}
module Evaluator where

import "base" Control.Monad (zipWithM)
import "base" Data.Foldable (fold)
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Product
import "base" Data.Maybe (isNothing, catMaybes, fromJust)
import "base" Data.Void
import "base" Data.Data
import "base" GHC.Generics

import "uniplate" Data.Generics.Uniplate.Data

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "data-fix" Data.Fix (Fix(..))

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "pretty" Text.PrettyPrint.Annotated (renderSpans)

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..), Name(..), NameFlavour(..))

import "recursion-schemes" Data.Functor.Foldable qualified as R

import Lift
import Ppr qualified as P

-- Utils

zipConcatM :: Monad m => (a -> b -> m [c]) -> [a] -> [b] -> m [c]
zipConcatM f as bs = concat <$> zipWithM f as bs

-- Evaluation

data Evaluable
  = EvalFunctionClauses [Clause] -- Dec.FunD
  | EvalValueDeclaration Pat Body [Dec] -- Dec.ValD
  | EvalExpression Exp -- Exp

type Environment = Map Name Evaluable

definitions :: Exp -> [(Name, Evaluable)]
definitions (LetE decs exp) = do
  dec <- decs
  case dec of
    FunD name clauses -> pure (name, EvalFunctionClauses clauses)
    ValD pat body decs -> do
      _ <- undefined
      []
    _ -> []

data ReductionFailure
  = AlreadyFullyReduced
  | NeedsSubReduction ExpKey
  | UnexpectedErrorReduce String ExpKey
  deriving (Show)

type ReductionSuccess = Exp
type ReductionMonad = Either ReductionFailure
type ReductionResult = ReductionMonad ReductionSuccess

tryReduce :: Environment -> Exp -> ReductionResult
tryReduce environment exp =
  let fullyReduced = Left AlreadyFullyReduced
      needsSubReduction expKey = Left $ NeedsReduction expKey
      unexpectedErrorReduce msg expKey = Left $ UnexpectedErrorReduce msg expKey
  in
  case exp of
    LitE _ -> fullyReduced
    CondE (ConE conName) true false
      | conName == 'True -> Right true
      | conName == 'False -> Right false
      | otherwise -> unexpectedErrorReduce "If expression given non-boolean constructor" undefined
    CondE cond true false -> do
      undefined

-- ============================ PATTERN MATCHING

-- Extract bound names from a pattern, mainly useful for determining which
-- pattern defines which variables in an environment
patNames' :: Pat -> [Name]
patNames' pat = [name | name@(Name _ flavour@(NameU _)) <- childrenBi pat]

-- Matching between patterns and expressions can fail in three ways:
-- - The pattern and the expression are known not to match
-- - The expression may or may not match the pattern - it needs to be reduced
--   further to say for certain
-- - The pattern and the expression are incompatible for pattern matching in
--   some way that the type system should have disallowed beforehand
data MatchFailure
  = Mismatch (PatKey, ExpKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | NeedsReduction (PatKey, ExpKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | UnexpectedErrorMatch String (PatKey, ExpKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch
  deriving (Show, Lift)

type MatchSuccess = [(Pat, Exp)]
type MatchMonad a = Either MatchFailure a
type MatchResult = MatchMonad MatchSuccess

matchPatKeyed :: Pat -> Exp -> MatchResult
matchPatKeyed pat exp = go (annKeys pat) (annKeys exp)
  where
    go :: Fix (RecKey Pat) -> Fix (RecKey Exp) -> MatchResult
    go annPat annExp = match patFAnn expFAnn
      where
        (patKey, patFAnn) = toKeyPair annPat
        (expKey, expFAnn) = toKeyPair annExp

        mismatch, needsReduction :: MatchMonad a
        mismatch = Left $ Mismatch (patKey, expKey)
        needsReduction = Left $ NeedsReduction (patKey, expKey)

        unexpectedError :: String -> MatchMonad a
        unexpectedError msg = Left $ UnexpectedErrorMatch msg (patKey, expKey)

        match :: PatF (Fix (RecKey Pat)) -> ExpF (Fix (RecKey Exp)) -> MatchResult
        match (LitPF pat) (LitEF exp)
          | pat == exp = Right []
          | otherwise = mismatch
        match (VarPF name) exp = Right [(VarP name, deannWrapped exp)]
        match (TupPF pats) (TupEF mexps)
          | length pats /= length mexps = unexpectedError "Tuple pattern-expression arity mismatch."
          | otherwise = do
              -- If there are any Nothing expressions, the tuple expression is partially applied and we short circuit with an error
              let onlyJust :: Maybe a -> MatchMonad a
                  onlyJust Nothing = unexpectedError "Tuple expression is not fully applied (e.g. is a partially applied tuple like (,,) or (1,))."
                  onlyJust (Just a) = pure a
              exps <- traverse onlyJust mexps
              zipConcatM go pats exps
        match (UnboxedTupPF _) _ = error "matchPatKeyed: Unsupported UnboxedTupP pattern in AST"
        match (UnboxedSumPF _ _ _) _ = error "matchPatKeyed: Unsupported UnboxedSumP pattern in AST"
        match (ConPF patConName pats) _
          | (func, margs) <- flattenAppsKeyed annExp
          , let args = catMaybes margs
          , (ConE expConName) <- deann func
          = if expConName /= patConName
              then mismatch -- if constructors are different, assume that they belong to the same ADT & are mismatched
                            -- TODO: How does this interact with PatternSynonyms?
                   -- if the pattern & expression constructors come from different ADTS, we'd return: `unexpectedError "Pattern and expression have different constructor names."`
                   -- alas, we can't do this comparison here, for now
              else case compare (length pats) (length args) of
                LT -> unexpectedError "Data constructor in expression is applied to too many arguments."
                GT -> unexpectedError "Data constructor in expression isn't fully applied."
                EQ -> zipConcatM go pats args
        match (InfixPF patL patConName patR) _
          | let pats = [patL, patR]
          , (func, margs) <- flattenAppsKeyed annExp
          , let args = catMaybes margs
          , (ConE expConName) <- deann func
          = if expConName /= patConName
              then mismatch -- if constructors are different, assume that they belong to the same ADT & are mismatched
                            -- TODO: How does this interact with PatternSynonyms?
                   -- if the pattern & expression constructors come from different ADTS, we'd return: `unexpectedError "Pattern and expression have different constructor names."`
                   -- alas, we can't do this comparison here, for now
              else case compare (length pats) (length args) of
                LT -> unexpectedError "Data constructor in expression is applied to too many arguments."
                GT -> unexpectedError "Data constructor in expression isn't fully applied."
                EQ -> zipConcatM go pats args
        match (UInfixPF patL _ patR) _ = error "matchPatKeyed: Unsupported pat UInfixP"
        match (ParensPF pat) exp = go pat annExp
        match pat (ParensEF exp) = go annPat exp
        match (TildePF pat) exp = Right [(deann pat, deannWrapped exp)] -- lazy patterns always match, deferred to a "let-desugaring"
        match (BangPF pat) exp = error "matchPatKeyed: Unsupported pat BangP"
        match (AsPF name pat) exp = do
          submatches <- go pat annExp
          pure $ (VarP name, deannWrapped exp) : submatches
        match WildPF _ = Right []
        match (RecPF _ fieldPats) _ = error "matchPatKeyed: Unsupported pat RecP" -- TODO: Urgently need to support field patterns
        match (ListPF pats) (ListEF exps) -- TODO: handle conses <=> list literals
          | length pats /= length exps = unexpectedError "List pattern and list expression have different lengths."
          | otherwise = zipConcatM go pats exps
        match (SigPF pat type_) _ = error "matchPatKeyed: Unsupported pat SigP"
        match (ViewPF exp pat) _ = error "matchPatKeyed: Unsupported pat ViewP"

        -- TODO: How does matching through lets & other scope-affecting nodes work? Must consider.
        -- Below enabled for demo purposes, not yet "stable"
        match pat (LetEF _ exp) = go annPat exp

        match pat exp
          -- TODO: Definitely unfinished cases here somewhere...
          | let (f, _) = flattenAppsKeyed annExp
          , (ConE _) <- deann f
          = mismatch
          | otherwise
          = needsReduction -- TODO: Consider how caller checks for forcing of an `error "msg"`

data FlattenApps a = FlattenApps
  { function :: a
  , args :: [a]
  }

flattenAppsF :: ExpF a -> Maybe (a, [Maybe a])
flattenAppsF (AppEF func arg) = Just (func, [Just arg])
flattenAppsF (InfixEF mlarg func mrarg) = Just (func, [mlarg, mrarg])
flattenAppsF exp = Nothing

flattenApps :: Exp -> (Exp, [Maybe Exp])
flattenApps = flattenAppsG id

flattenAppsKeyed :: Fix (RecKey Exp) -> (Fix (RecKey Exp), [Maybe (Fix (RecKey Exp))])
flattenAppsKeyed = flattenAppsG (\(Pair _ expf) -> expf)

flattenAppsG
  :: (R.Recursive t, R.Base t ~ f)
  => (forall a. f a -> ExpF a)
  -> t -> (t, [Maybe t])
flattenAppsG extractExpression self =
  case flattenAppsF (extractExpression $ R.project self) of
    Nothing -> (self, [])
    Just (function, postArgs) ->
      let (innermostFunction, preArgs) = flattenAppsG extractExpression function
      in
      (innermostFunction, subtituteOnto preArgs postArgs)
  where
    subtituteOnto :: [Maybe a] -> [Maybe a] -> [Maybe a]
    subtituteOnto [] postArgs = postArgs
    subtituteOnto preArgs [] = preArgs
    subtituteOnto (preArg:preRest) (postArg:postRest)
      | isNothing preArg = postArg : subtituteOnto preRest postRest
      | otherwise = preArg : subtituteOnto preRest (postArg:postRest)
