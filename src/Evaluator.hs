{-# LANGUAGE DeriveFunctor #-}
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
import "base" Data.Bifunctor
import "base" Data.Foldable (fold)
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Product
import "base" Data.Maybe (isNothing, catMaybes, fromJust)
import "base" Data.Void
import "base" GHC.Generics

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "data-fix" Data.Fix (Fix(..))

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "pretty" Text.PrettyPrint.Annotated (renderSpans)

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..))

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

patNames :: Pat -> [Name]
patNames (LitP _) = []
patNames (VarP name) = [name]
patNames (TupP pats) = foldMap patNames pats
patNames (UnboxedTupP _) = error "patNames: Unsupported pat UnboxedTupP"
patNames (UnboxedSumP _ _ _) = error "patNames: Unsupported pat UnboxedSumP"
patNames (ConP _ pats) = foldMap patNames pats
patNames (InfixP patL _ patR) = foldMap patNames [patL, patR]
patNames (UInfixP patL _ patR) = error "patNames: Unsupported pat UInfixP"
patNames (ParensP pat) = patNames pat
patNames (TildeP pat) = patNames pat -- TODO: How does laziness affect the use of patNames?
patNames (BangP pat) = patNames pat
patNames (AsP name pat) = name : patNames pat
patNames (WildP) = []
patNames (RecP _ fieldPats) = foldMap (patNames . snd) fieldPats
patNames (ListP pats) = foldMap patNames pats
patNames (SigP pat type_) = error "patNames: Unsupported pat SigP"
patNames (ViewP exp pat) = error "patNames: Unsupported pat ViewP"

data ReductionResult a
  = NoReductionsAvailable
  | ReduceErrors [String]
  | ReductionMade a
  deriving (Show, Functor)

instance Applicative ReductionResult where
  pure = ReductionMade
  NoReductionsAvailable <*> (ReduceErrors es) = ReduceErrors es
  (ReduceErrors es) <*> NoReductionsAvailable = ReduceErrors es
  (ReduceErrors es) <*> (ReduceErrors es') = ReduceErrors $ es ++ es'
  NoReductionsAvailable <*> _ = NoReductionsAvailable
  _ <*> NoReductionsAvailable = NoReductionsAvailable
  (ReductionMade f) <*> (ReductionMade x) = ReductionMade $ f x

instance Monad ReductionResult where
  (>>=) x f = join $ f <$> x
    where
      join (ReductionMade y) = y
      join (ReduceErrors es) = ReduceErrors es
      join NoReductionsAvailable = NoReductionsAvailable

tryReduce :: Environment -> Exp -> ReductionResult Exp
tryReduce environment exp =
  case exp of
    LitE _ -> NoReductionsAvailable
    CondE (ConE conName) true false
      | conName == 'True -> ReductionMade true
      | conName == 'False -> ReductionMade false
      | otherwise -> ReduceErrors ["Condition given non-boolean constructor"]
    CondE cond true false -> do
      undefined

data MatchFailure
  = Mismatch (PatKey, ExpKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | NeedsReduction (PatKey, ExpKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | UnexpectedError String (PatKey, ExpKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch
  deriving (Show, Lift)

type MatchSuccess = [(Pat, Exp)]
type MatchMonad a = Either MatchFailure a
type MatchResult = MatchMonad MatchSuccess

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

deann :: R.Corecursive t => Fix (RecKey t) -> t
deann = R.hoist (\(Pair _ tf) -> tf)

deannWrapped :: R.Corecursive t => R.Base t (Fix (RecKey t)) -> t
deannWrapped = R.embed . fmap deann

toKeyPair :: Fix (Ann a f) -> (a, f (Fix (Ann a f)))
toKeyPair (Fix (Pair (Const key) expf)) = (key, expf)

toKeyPairDeann :: R.Corecursive t => Fix (RecKey t) -> ([Key (R.Base t)], t)
toKeyPairDeann ann =
  let (key, expf) = toKeyPair ann
  in
  (key, R.embed $ fmap deann expf)

-- TODO: Handle infix applications & type applications (URGENT!)
flattenAppsKeyed :: Fix (RecKey Exp) -> (Fix (RecKey Exp), [Fix (RecKey Exp)])
flattenAppsKeyed = fmap reverse . go
  where
    -- Build up argument list in reverse, to avoid O(n^2)
    go :: Fix (RecKey Exp) -> (Fix (RecKey Exp), [Fix (RecKey Exp)])
    go (Fix (Pair _ (AppEF func arg))) = (arg :) <$> go func
    go exp = (exp, [])

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
        unexpectedError msg = Left $ UnexpectedError msg (patKey, expKey)

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
          | (func, args) <- flattenAppsKeyed annExp
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
        match (InfixPF patL _ patR) _ = error "matchPatKeyed: Unsupported pat InfixP" -- TODO: Urgently need to support this for cons
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
        match (ListPF pats) (ListEF exps)
          | length pats /= length exps = unexpectedError "List pattern and list expression have different lengths."
          | otherwise = zipConcatM go pats exps
        match (SigPF pat type_) _ = error "matchPatKeyed: Unsupported pat SigP"
        match (ViewPF exp pat) _ = error "matchPatKeyed: Unsupported pat ViewP"

        -- TODO: How does matching through lets & other scope-affecting nodes work? Must consider.
        -- Below enabled for demo purposes, not yet "stable"
        match pat (LetEF _ exp) = go annPat exp

        match pat exp
          -- TODO: Definitely unfinished cases here somewhere...
          | let (f, args) = flattenAppsKeyed annExp
          , (ConE _) <- deann f
          = mismatch
          | otherwise
          = needsReduction -- TODO: Consider how caller checks for forcing of an `error "msg"`

e2eMatchDemo :: Q Pat -> Q Exp -> Q Exp
e2eMatchDemo mpat mexp = do
  pat <- mpat
  exp <- mexp
  case matchPatKeyed pat exp of
    Left (Mismatch (patKey, expKey)) ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.orange "Following pattern and expression do not match."
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.attachAnn patKey (P.Annotation P.orange Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.attachAnn expKey (P.Annotation P.orange Nothing) (P.noann exp))
        ]
    Left (NeedsReduction (patKey, expKey)) ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.purple "Following expression needs further reduction to conclusively match."
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.attachAnn patKey (P.Annotation P.purple Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.attachAnn expKey (P.Annotation P.purple Nothing) (P.noann exp))
        ]
    Left (UnexpectedError msg (patKey, expKey)) ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.red "Unexpected error (type system should catch this!): " ++ show msg
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.attachAnn patKey (P.Annotation P.red Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.attachAnn expKey (P.Annotation P.red Nothing) (P.noann exp))
        ]
    Right bound ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.green "Following pattern and expression match."
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.noann pat)
        , P.boldByANSI "expression: ", P.pprintColoured (P.noann exp)
        ]
  lift ()

e2eMatchExample :: Q Exp
e2eMatchExample = do
  runIO $ putStrLn ""
  e2eMatchDemo [p| (Just 1, Just _) |] [e| (Just 1, Nothing) |]
  e2eMatchDemo [p| (Just 1, Just _) |] [e| (Just 1, x) |]
  e2eMatchDemo [p| (Just 1, Just _) |] [e| (Just 1, Just x) |]
  e2eMatchDemo [p| Just _ |] [e| let x = 2 in Nothing |]
  e2eMatchDemo [p| Just 2 |] [e| let x = 2 in Just x |]
  e2eMatchDemo [p| Just _ |] [e| let x = 2 in Just x |]
  e2eMatchDemo [p| (Just 1, Just 2) |] [e| (Just 1, let x = 2 in Nothing) |]
  lift ()

p = $(lift =<< [p| (Just 2, Just Nothing) |])
e = $(lift =<< [e| (Just 2, Just x) |])
(patkey, expkey) =
  case matchPatKeyed p e of
    Left (Mismatch keys) -> keys
    Left (NeedsReduction keys) -> keys
    Left (UnexpectedError msg keys) -> keys
    Right _ -> error "can't make patKey / expKey because expressions match"
