{-# LANGUAGE DeriveFunctor #-}
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

data MatchResult
  = MatchReduceError String
  | SuccessfulMatch [(Name, Exp)]

data InfixArgIndex = LArg | RArg

data PatFI
  = LitPFI Void
  | VarPFI Void
  | TupPFI Int
  | UnboxedTupPFI Int
  | UnboxedSumPFI
  | ConPFI Int
  | InfixPFI InfixArgIndex
  | UInfixPFI InfixArgIndex
  | ParensPFI
  | TildePFI
  | BangPFI
  | AsPFI
  | WildPFI Void
  | RecPFI Int
  | ListPFI Int
  | SigPFI
  | ViewPFI

getPat :: [PatFI] -> Pat -> Maybe Pat
getPat [] pat = Just pat
getPat (i:rest) pat = getPat rest =<< getPatF i (R.project pat)

modPat :: [PatFI] -> Pat -> (Pat -> Pat) -> Pat
modPat is pat f = go is pat
  where
    go [] pat = f pat
    go (i:rest) pat = R.embed $ modPatF i (R.project pat) (go rest)

getPatF :: PatFI -> PatF a -> Maybe a
getPatF (TupPFI i) (TupPF ps) = Just $ ps !! i
getPatF (UnboxedTupPFI i) (UnboxedTupPF ps) = Just $ ps !! i
getPatF (ConPFI i) (ConPF _ ps) = Just $ ps !! i
getPatF (InfixPFI LArg) (InfixPF l _ _) = Just l
getPatF (InfixPFI RArg) (InfixPF _ _ r) = Just r
getPatF (UInfixPFI LArg) (UInfixPF l _ _) = Just l
getPatF (UInfixPFI RArg) (UInfixPF _ _ r) = Just r
getPatF (RecPFI i) (RecPF _ nps) = Just $ snd $ nps !! i
getPatF (ListPFI i) (ListPF ps) = Just $ ps !! i

modPatF :: PatFI -> PatF a -> (a -> a) -> PatF a
modPatF (TupPFI i) (TupPF ps) f = TupPF $ updateList i ps f
modPatF (UnboxedTupPFI i) (UnboxedTupPF ps) f = UnboxedTupPF $ updateList i ps f
modPatF (ConPFI i) (ConPF name ps) f = ConPF name $ updateList i ps f
modPatF (InfixPFI LArg) (InfixPF l name r) f = InfixPF (f l) name r
modPatF (InfixPFI RArg) (InfixPF l name r) f = InfixPF l name (f r)
modPatF (UInfixPFI LArg) (UInfixPF l name r) f = UInfixPF (f l) name r
modPatF (UInfixPFI RArg) (UInfixPF l name r) f = UInfixPF l name (f r)
modPatF (RecPFI i) (RecPF name nps) f = RecPF name (updateList i nps (fmap f))
modPatF (ListPFI i) (ListPF ps) f = ListPF $ updateList i ps f

annPat :: PatF a -> PatF (PatFI, a)
annPat = undefined

data ExpIndex

getExp :: ExpIndex -> ExpF a -> a
getExp = undefined

setExp :: ExpIndex -> ExpF a -> a -> a
setExp = undefined

patIndexToExpIndex :: PatFI -> ExpIndex
patIndexToExpIndex = undefined
