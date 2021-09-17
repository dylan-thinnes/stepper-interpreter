{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
module Evaluator where

import Data.Foldable (fold)
import Data.Maybe (isNothing, catMaybes)

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "template-haskell" Language.Haskell.TH

import Lift

-- Utils

prexp :: Q Exp -> Q Exp
prexp qexp = [| putStrLn $(qexp >>= stringE . pprint) |]

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
  = Success [(Name, Exp)]
  | AwaitingApplication
  | Failure [String]
  deriving (Show)

instance Semigroup PatternMatch where
  -- Failures override AwaitingApplication or Successes
  (<>) (Failure lMsgs) (Failure rMsgs) = Failure $ lMsgs ++ rMsgs
  (<>) (Failure lMsgs) _ = Failure lMsgs
  (<>) _ (Failure rMsgs) = Failure rMsgs

  -- AwaitingApplication overrides Successes
  (<>) AwaitingApplication _ = AwaitingApplication
  (<>) _ AwaitingApplication = AwaitingApplication

  -- Successful matches merge
  (<>) (Success lMatches) (Success rMatches) = Success $ lMatches ++ rMatches

instance Monoid PatternMatch where
  mempty = Success []

flattenApps :: Exp -> (Exp, [Exp])
flattenApps = fmap reverse . go
  where
    -- Build up argument list in reverse, to avoid O(n^2)
    go (AppE f arg) = fmap (arg:) $ go f
    go exp = (exp, [])

matchPat :: Pat -> Exp -> PatternMatch
matchPat (LitP pat) (LitE exp)
  | pat == exp = Success []
  | otherwise = Failure [concat ["Literals unequal: pattern ", show pat, ", expression ", show exp, "."]]
matchPat (VarP name) exp = Success [(name, exp)]
matchPat (TupP pats) (TupE exps)
  | length pats /= length exps = Failure ["Tuples are of different lengths."]
  | any isNothing exps = Failure ["Cannot pattern match over partially applied tuples."]
  | otherwise = fold $ zipWith matchPat pats (catMaybes exps)
matchPat (UnboxedTupP _) _ = error "matchPat: Unsupported pat UnboxedTupP"
matchPat (UnboxedSumP _ _ _) _ = error "matchPat: Unsupported pat UnboxedSumP"
matchPat (ConP patConName pats) exp =
  let (f, args) = flattenApps exp
  in
  case f of
    ConE expConName
      | expConName /= patConName -> Failure ["Pattern and expression have different constructor names."]
      | length pats /= length args -> Failure ["Pattern and expression have different number of args to constructors - is the expression constructor partially applied?"]
      | otherwise -> fold $ zipWith matchPat pats args
    _ -> Failure ["Expression is not a data construction."]
-- matchPat (InfixP patL _ patR) _ = undefined
matchPat (UInfixP patL _ patR) _ = error "matchPat: Unsupported pat UInfixP"
matchPat (ParensP pat) exp = matchPat pat exp
matchPat pat (ParensE exp) = matchPat pat exp
-- matchPat (TildeP pat) _ = undefined -- TODO: How does laziness affect the use of matchPat?
-- matchPat (BangP pat) _ = undefined
matchPat (AsP name pat) exp = Success [(name, exp)] <> matchPat pat exp
matchPat WildP _ = Success []
-- matchPat (RecP _ fieldPats) _ = undefined
matchPat (ListP pats) (ListE exps)
  | length pats /= length exps = Failure ["List pattern and list expression have different lengths."]
  | otherwise = fold $ zipWith matchPat pats exps
matchPat (SigP pat type_) _ = error "matchPat: Unsupported pat SigP"
matchPat (ViewP exp pat) _ = error "matchPat: Unsupported pat ViewP"
matchPat _ _ = Failure ["Pattern and expression do not match."] -- TODO: Is this exhaustive enough?

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
