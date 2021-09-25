{-# LANGUAGE DeriveFunctor #-}
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
import "base" Data.Maybe (isNothing, catMaybes, fromJust)
import "base" Data.Void
import "base" GHC.Generics

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..))

import Lift

R.makeBaseFunctor ''Exp
R.makeBaseFunctor ''Pat

-- Utils

prexp :: Q Exp -> Q Exp
prexp qexp = [| putStrLn $(qexp >>= stringE . pprint) |]

updateList :: Int -> [a] -> (a -> a) -> [a]
updateList i l f
  | 0 <= i && i < length l = take i l ++ [f $ l !! i] ++ drop (i + 1) l
  | otherwise = l

setList :: Int -> [a] -> a -> [a]
setList i l x = updateList i l (const x)

dekeyed :: Functor f => f (Key f, a) -> f a
dekeyed = fmap snd

projectK :: (R.Recursive t, Keyed (R.Base t)) => t -> R.Base t (Key (R.Base t), t)
projectK = keyed . R.project

embedK :: (R.Corecursive t, Keyed (R.Base t)) => R.Base t (Key (R.Base t), t) -> t
embedK = R.embed . dekeyed

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

data PatternMatch
  = Success [Either (Pat, Exp) (Name, Exp)]
  | Failure [String]
  deriving (Show)

instance Semigroup PatternMatch where
  -- Failures override Successes
  (<>) (Failure lMsgs) (Failure rMsgs) = Failure $ lMsgs ++ rMsgs
  (<>) (Failure lMsgs) _ = Failure lMsgs
  (<>) _ (Failure rMsgs) = Failure rMsgs

  -- Successful matches merge
  (<>) (Success lMatches) (Success rMatches) = Success $ lMatches ++ rMatches

instance Monoid PatternMatch where
  mempty = Success []

flattenApps :: Exp -> (Exp, [Exp]) -- TODO: Handle infix applications & type applications
flattenApps = fmap reverse . go
  where
    -- Build up argument list in reverse, to avoid O(n^2)
    go (AppE f arg) = fmap (arg:) $ go f
    go exp = (exp, [])

matchPat :: Pat -> Exp -> PatternMatch
matchPat (LitP pat) (LitE exp)
  | pat == exp = Success []
  | otherwise = Failure [concat ["Literals don't match: pattern ", show pat, ", expression ", show exp, "."]]
matchPat (VarP name) exp = Success [Right (name, exp)]
matchPat (TupP pats) (TupE exps)
  | length pats /= length exps = Failure ["Tuples are of different lengths."]
  | any isNothing exps = Failure ["Cannot pattern match over partially applied tuples."]
  | otherwise = fold $ zipWith matchPat pats (catMaybes exps)
matchPat (UnboxedTupP _) _ = error "matchPat: Unsupported pat UnboxedTupP"
matchPat (UnboxedSumP _ _ _) _ = error "matchPat: Unsupported pat UnboxedSumP"
matchPat (ConP patConName pats) exp
  | (ConE expConName, args) <- flattenApps exp
  = if
      | expConName /= patConName -> Failure ["Pattern and expression have different constructor names."]
      | length pats /= length args -> Failure ["Pattern and expression have different number of args to constructors - is the expression constructor partially applied?"]
      | otherwise -> fold $ zipWith matchPat pats args
-- matchPat (InfixP patL _ patR) _ = undefined
matchPat (UInfixP patL _ patR) _ = error "matchPat: Unsupported pat UInfixP"
matchPat (ParensP pat) exp = matchPat pat exp
matchPat pat (ParensE exp) = matchPat pat exp
-- matchPat (TildeP pat) _ = undefined -- TODO: How does laziness affect the use of matchPat?
-- matchPat (BangP pat) _ = undefined
matchPat (AsP name pat) exp = Success [Right (name, exp)] <> matchPat pat exp
matchPat WildP _ = Success []
-- matchPat (RecP _ fieldPats) _ = undefined
matchPat (ListP pats) (ListE exps)
  | length pats /= length exps = Failure ["List pattern and list expression have different lengths."]
  | otherwise = fold $ zipWith matchPat pats exps
matchPat (SigP pat type_) _ = error "matchPat: Unsupported pat SigP"
matchPat (ViewP exp pat) _ = error "matchPat: Unsupported pat ViewP"
matchPat pat exp =
  let (f, args) = flattenApps exp
  in
  if
    | length args == 0
    -> Failure ["Pattern and expression do not match."]
    | (ConE _) <- f
    -> Failure ["Pattern and expression do not match."]
    | (VarE fName) <- f
    , show fName == "GHC.Err.error" -- TODO: Check fName is error w/o string-typing
    -> Failure ["Pattern forces the evaluation of an error."]
    | otherwise
    -> Success [Left (pat, exp)]

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

data MatchFailure
  = Mismatch (PatKey, ExpKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | NeedsReduction (PatKey, ExpKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | UnexpectedError String (PatKey, ExpKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch

type MatchSuccess = [(Pat, Exp)]
type MatchMonad a = Either MatchFailure a
type MatchResult = MatchMonad MatchSuccess

mismatch, needsReduction :: MatchMonad a
mismatch = Left $ Mismatch ([], [])
needsReduction = Left $ NeedsReduction ([], [])

unexpectedError :: String -> MatchMonad a
unexpectedError msg = Left $ UnexpectedError msg ([], [])

prependMatchFailure :: (PatKey, ExpKey) -> MatchFailure -> MatchFailure
prependMatchFailure (prePatKey, preExpKey) failure =
  case failure of
    UnexpectedError msg (patKey, expKey) -> UnexpectedError msg (prePatKey ++ patKey, preExpKey ++ expKey)
    Mismatch (patKey, expKey) -> Mismatch (prePatKey ++ patKey, preExpKey ++ expKey)
    NeedsReduction (patKey, expKey) -> NeedsReduction (prePatKey ++ patKey, preExpKey ++ expKey)

withPreKeys :: (PatKey, ExpKey) -> MatchResult -> MatchResult
withPreKeys prekeys = first $ prependMatchFailure prekeys

matchPatKeyed :: Pat -> Exp -> MatchResult
matchPatKeyed pat exp = go (projectK pat) (projectK exp)
  where
    rec = matchPatKeyed

    matchWithPreKeys :: (PatKey, Pat) -> (ExpKey, Exp) -> MatchResult
    matchWithPreKeys (prePatKey, pat) (preExpKey, exp) =
      withPreKeys (prePatKey, preExpKey) $ rec pat exp

    listifyKey :: (a, b) -> ([a], b)
    listifyKey = first (\x -> [x])

    prependKey :: a -> ([a], b) -> ([a], b)
    prependKey a = first (a :)

    -- TODO: Handle infix applications & type applications
    -- Could simplify as catamorphism w/ Compose (ExpKey,) ExpF ??
    flattenApps :: ExpF (Key ExpF, Exp) -> ((ExpKey, Exp), [(ExpKey, Exp)])
    flattenApps = fmap reverse . go
      where
        -- Build up argument list in reverse, to avoid O(n^2)
        go :: ExpF (Key ExpF, Exp) -> ((ExpKey, Exp), [(ExpKey, Exp)])
        go (AppEF (fKey, f) (argKey, arg)) =
          let (deepF, deepArgs) = go $ projectK f
          in
          (prependKey fKey deepF, ([argKey], arg) : map (prependKey fKey) deepArgs)
        go exp = (([], embedK exp), [])

    go :: PatF (Key PatF, Pat) -> ExpF (Key ExpF, Exp) -> MatchResult
    go (LitPF pat) (LitEF exp)
      | pat == exp = Right []
      | otherwise = mismatch
    go (VarPF name) exp = Right [(VarP name, embedK exp)]
    go (TupPF pats) (TupEF mexps)
      | length pats /= length mexps = unexpectedError "Tuple pattern-expression arity mismatch."
      | otherwise = do
          -- If there are any Nothing expressions, the tuple expression is partially applied and we short circuit with an error
          let onlyJust Nothing = unexpectedError "Tuple expression is not fully applied (e.g. is a partially applied tuple like (,,) or (1,))."
              onlyJust (Just a) = pure a
          exps <- traverse onlyJust mexps
          zipConcatM matchWithPreKeys (listifyKey <$> pats) (listifyKey <$> exps)
    go (UnboxedTupPF _) _ = error "matchPatKeyed: Unsupported UnboxedTupP pattern in AST"
    go (UnboxedSumPF _ _ _) _ = error "matchPatKeyed: Unsupported UnboxedSumP pattern in AST"
    go (ConPF patConName pats) exp
      | ((_, ConE expConName), args) <- flattenApps exp
      = if expConName /= patConName
          then unexpectedError "Pattern and expression have different constructor names."
          else case compare (length pats) (length args) of
            LT -> unexpectedError "Data constructor in expression is applied to too many arguments."
            GT -> unexpectedError "Data constructor in expression isn't fully applied."
            EQ -> zipConcatM matchWithPreKeys (listifyKey <$> pats) args
    go (InfixPF patL _ patR) _ = error "matchPatKeyed: Unsupported pat InfixP" -- TODO: Urgently need to support this for cons
    go (UInfixPF patL _ patR) _ = error "matchPatKeyed: Unsupported pat UInfixP"
    go (ParensPF (patKey, pat)) exp = matchWithPreKeys ([patKey], pat) ([], embedK exp)
    go pat (ParensEF (expKey, exp)) = matchWithPreKeys ([], embedK pat) ([expKey], exp)
    go (TildePF (patKey, pat)) exp = Right [(pat, embedK exp)] -- lazy patterns always match, deferred to a "let-desugaring"
    go (BangPF pat) exp = error "matchPatKeyed: Unsupported pat BangP"
    go (AsPF name pat) exp = do
      submatches <- matchWithPreKeys (listifyKey pat) ([], embedK exp)
      pure $ (VarP name, embedK exp) : submatches
    go WildPF _ = Right []
    go (RecPF _ fieldPats) _ = error "matchPatKeyed: Unsupported pat RecP" -- TODO: Urgently need to support field patterns
    go (ListPF pats) (ListEF exps)
      | length pats /= length exps = unexpectedError "List pattern and list expression have different lengths."
      | otherwise = zipConcatM matchWithPreKeys (listifyKey <$> pats) (listifyKey <$> exps)
    go (SigPF pat type_) _ = error "matchPatKeyed: Unsupported pat SigP"
    go (ViewPF exp pat) _ = error "matchPatKeyed: Unsupported pat ViewP"
    go pat exp =
      let ((_, f), args) = flattenApps exp
      in
      if
        | length args == 0
        -> mismatch
        | (ConE _) <- f
        -> mismatch
        -- | (VarE fName) <- f
        -- , show fName == "GHC.Err.error" -- TODO: Check fName is error w/o string-typing
        -- -> Failure ["Pattern forces the evaluation of an error."]
        | otherwise
        -> needsReduction -- TODO: Consider how receiver checks for forcing of an `error "msg"`
