{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import "base" Control.Monad (zipWithM, ap)
import "base" Data.Foldable (fold, toList)
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Product
import "base" Data.Functor.Identity
import "base" Data.Either (isRight, partitionEithers)
import "base" Data.Maybe (isNothing, catMaybes, fromJust, mapMaybe)
import "base" Data.Void
import "base" Data.Data
import "base" GHC.Generics

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "data-fix" Data.Fix (Fix(..))

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "mtl" Control.Monad.Reader hiding (lift)
import "mtl" Control.Monad.Except hiding (lift)

import "pretty" Text.PrettyPrint.Annotated (renderSpans)

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..), Name(..), NameFlavour(..))

import "uniplate" Data.Generics.Uniplate.Data

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import Lift
import Ppr qualified as P

import Debug.Trace

-- Utils

zipConcatM :: Monad m => (a -> b -> m [c]) -> [a] -> [b] -> m [c]
zipConcatM f as bs = concat <$> zipWithM f as bs

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
    go annPat annExp = matchLists annPat annExp
      where
        (patKey, patFAnn) = toKeyPair annPat
        (expKey, expFAnn) = toKeyPair annExp

        mismatch, needsReduction :: MatchMonad a
        mismatch = Left $ Mismatch (patKey, expKey)
        needsReduction = Left $ NeedsReduction (patKey, expKey)

        unexpectedError :: String -> MatchMonad a
        unexpectedError msg = Left $ UnexpectedErrorMatch msg (patKey, expKey)

        matchLists :: Fix (RecKey Pat) -> Fix (RecKey Exp) -> MatchResult
        matchLists pat exp =
          let patList = patToIsListKeyed pat
              expList = expToIsListKeyed exp
          in
          case (patList, expList) of
            -- Matching conses
            (IsCons head1 tail1, IsCons head2 tail2) ->
              zipConcatM go [head1, tail1] [head2, tail2]
            (IsCons head1 tail1, IsLiteral (head2:tail2)) ->
              zipConcatM go [head1, tail1] [head2, fromKeyPair expKey $ ListEF tail2]
            (IsLiteral (head1:tail1), IsCons head2 tail2) ->
              zipConcatM go [head1, fromKeyPair patKey $ ListPF tail1] [head2, tail2]

            -- Matching empty lists
            (IsNil _, IsNil _) -> Right []
            (IsNil _, IsLiteral []) -> Right []
            (IsLiteral [], IsNil _) -> Right []

            -- Mismatching conses to empty lists
            (IsCons _ _, IsNil _) -> mismatch
            (IsNil _, IsCons _ _) -> mismatch
            (IsCons _ _, IsLiteral []) -> mismatch
            (IsLiteral [], IsCons _ _) -> mismatch

            -- Try matches by other means
            _ -> match patFAnn expFAnn

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
          | FlattenedApps { func, args = margs } <- flattenAppsKeyed annExp
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
          , FlattenedApps { func, args = margs } <- flattenAppsKeyed annExp
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
          | FlattenedApps { func } <- flattenAppsKeyed annExp
          , (ConE _) <- deann func
          = mismatch
          | (ConP _ _) <- deann annPat -- May be too aggressive...
          = needsReduction
          | otherwise
          = needsReduction -- TODO: Consider how caller checks for forcing of an `error "msg"`

patExpPairToValDecl :: (Pat, Exp) -> Maybe Dec
patExpPairToValDecl (VarP patName, VarE expName) | patName == expName = Nothing
patExpPairToValDecl (pat, exp) = Just $ ValD pat (NormalB exp) []

-- ================== FUNCTION APPLICATION IN EXPRESSIONS

data FlattenedApps a = FlattenedApps
  { func :: a
  , args :: [Maybe a]
  , intermediateFuncs :: [(Int, a)]
  }
  deriving Show

getIntermediateFunc :: Int -> [(Int, a)] -> (Int, Int, a)
getIntermediateFunc n [] = error "getIntermediateFunc: ran out of functions"
getIntermediateFunc n ((size, f):rest)
  | n <= size = (n, size, f)
  | otherwise = getIntermediateFunc (n - size) rest

flattenAppsF :: (a, ExpF a) -> Maybe (FlattenedApps a)
flattenAppsF (orig, AppEF func arg) = Just $ FlattenedApps func [Just arg] [(1, orig)]
flattenAppsF (orig, InfixEF mlarg func mrarg) = Just $ FlattenedApps func [mlarg, mrarg] [(2, orig)]
flattenAppsF _ = Nothing

flattenApps :: Exp -> FlattenedApps Exp
flattenApps = flattenAppsG id

flattenAppsKeyed :: Fix (RecKey Exp) -> FlattenedApps (Fix (RecKey Exp))
flattenAppsKeyed = flattenAppsG (\(Pair _ expf) -> expf)

flattenAppsG
  :: (R.Recursive t, R.Base t ~ f)
  => (forall a. f a -> ExpF a)
  -> t -> FlattenedApps t
flattenAppsG extractExpression self =
  case flattenAppsF (self, extractExpression $ R.project self) of
    Nothing -> FlattenedApps self [] []
    Just (FlattenedApps { func, args = postArgs, intermediateFuncs = postIntermediateFuncs }) ->
      let FlattenedApps { func = innermostFunction, args = preArgs, intermediateFuncs = preIntermediateFuncs } =
            flattenAppsG extractExpression func
      in
      FlattenedApps innermostFunction (subtituteOnto preArgs postArgs) (preIntermediateFuncs ++ postIntermediateFuncs)
  where
    subtituteOnto :: [Maybe a] -> [Maybe a] -> [Maybe a]
    subtituteOnto [] postArgs = postArgs
    subtituteOnto preArgs [] = preArgs
    subtituteOnto (preArg:preRest) (postArg:postRest)
      | isNothing preArg = postArg : subtituteOnto preRest postRest
      | otherwise = preArg : subtituteOnto preRest (postArg:postRest)

-- ================= Lists Made From Literals, Cons, and []

data IsList a
  = IsCons a a
  | IsNil a
  | IsLiteral [a]
  | NotList
  deriving (Show, Eq, Functor)

isList :: IsList a -> Bool
isList NotList = False
isList _ = True

expToIsList :: Exp -> IsList Exp
expToIsList = expToIsListG id

expToIsListKeyed :: Fix (RecKey Exp) -> IsList (Fix (RecKey Exp))
expToIsListKeyed = expToIsListG (\(Pair _ expf) -> expf)

expToIsListG
  :: (R.Recursive t, R.Base t ~ f)
  => (forall a. f a -> ExpF a)
  -> t -> IsList t
expToIsListG extractExpression exp
  -- A cons constructor, applied to two expressions
  | FlattenedApps { func, args = Just headArg:Just tailArg:_ } <- flattenAppsG extractExpression exp
  , ConEF expConName <- extractExpression $ R.project func
  , expConName == '(:)
  = IsCons headArg tailArg
  -- A nil constructor
  | ConEF expConName <- extractExpression $ R.project exp
  , expConName == '[]
  = IsNil exp
  -- A list expression
  | (ListEF exps) <- extractExpression $ R.project exp
  = IsLiteral exps
  -- Otherwise, this isn't a list
  | otherwise
  = NotList

patToIsList :: Pat -> IsList Pat
patToIsList = patToIsListG id

patToIsListKeyed :: Fix (RecKey Pat) -> IsList (Fix (RecKey Pat))
patToIsListKeyed = patToIsListG (\(Pair _ patf) -> patf)

patToIsListG
  :: (R.Recursive t, R.Base t ~ f)
  => (forall a. f a -> PatF a)
  -> t -> IsList t
patToIsListG extractPattern pat
  -- A cons constructor, applied to two expressions, prefix
  | ConPF patConName [headArg, tailArg] <- extractPattern $ R.project pat
  , patConName == '(:)
  = IsCons headArg tailArg
  -- A cons constructor, applied to two expressions, infix
  | InfixPF headArg patConName tailArg <- extractPattern $ R.project pat
  , patConName == '(:)
  = IsCons headArg tailArg
  -- A nil constructor
  | ConPF expConName [] <- extractPattern $ R.project pat
  , expConName == '[]
  = IsNil pat
  -- A list expression
  | (ListPF pats) <- extractPattern $ R.project pat
  = IsLiteral pats
  -- Otherwise, this isn't a list
  | otherwise
  = NotList

-- =============================== Evaluation

data Declarable
  = FunctionDeclaration FunctionDeclaration -- let f <1st clause>; f <2nd clause> ...
  | ValueDeclaration Pat Body [Dec] -- let <pat> = <body> where <...decs>
  | DataField Pat Exp -- field for a datatype, e.g. MyDatatype { myField :: Int }
  deriving (Show)

data FunctionDeclaration
  = ClausesFD [Clause]
  | CustomFD Int (CustomShow ([Exp] -> Either (Int, MatchFailure) Exp))
    -- "escape hatch" for functions w/ strict cardinality, like (+), can force reduction of nth argument
    -- TODO: Implement full MatchResult generality for CustomFD
  deriving (Show)

data CustomShow a = CustomShow { msg :: String, unCustomShow :: a }
instance Show (CustomShow a) where
  show (CustomShow msg _) = msg

-- TODO: Deal with environment clobbering names that are used repeatedly, i.e. let a = 1 in let a = a + 4 in a
type Environment = Map Name Declarable

defaultEnvironment :: Environment
defaultEnvironment = mkEnvironment [('(+), plus), ('(*), times)]
  where
    plus = FunctionDeclaration $ CustomFD 2 (CustomShow "(+)" handler')
      where
        handler' [a, b] = handler a b
        handler' _ = error "defaultEnvironment/plus/handler': wrong number of arguments given to (+), this shouldn't happen!"

        handler (LitE (IntegerL a)) (LitE (IntegerL b)) = Right $ LitE $ IntegerL $ a + b
        handler a@(LitE _) b@(LitE _) = error $ unwords ["Incompatible lits", show a, show b, "supplied"]
        handler (LitE _) _ = Left (1, NeedsReduction ([], []))
        handler _ _ = Left (0, NeedsReduction ([], []))

    times = FunctionDeclaration $ CustomFD 2 (CustomShow "(*)" handler')
      where
        handler' [a, b] = handler a b
        handler' _ = error "defaultEnvironment/plus/handler': wrong number of arguments given to (+), this shouldn't happen!"

        handler (LitE (IntegerL a)) (LitE (IntegerL b)) = Right $ LitE $ IntegerL $ a * b
        handler a@(LitE _) b@(LitE _) = error $ unwords ["Incompatible lits", show a, show b, "supplied"]
        handler (LitE _) _ = Left (1, NeedsReduction ([], []))
        handler _ _ = Left (0, NeedsReduction ([], []))

mkEnvironment :: [(Name, Declarable)] -> Environment
mkEnvironment = M.fromList

addNewEnvs :: Environment -> [Environment] -> Environment
addNewEnvs env news = foldl updateEnv env news
  where
    updateEnv :: Environment -> Environment -> Environment
    updateEnv env new = M.unionWith const new env

defines :: Dec -> Environment
defines = mkEnvironment . go
  where
  go (FunD name clauses) = [(name, FunctionDeclaration $ ClausesFD clauses)]
  go (ValD pat body wheres) = [(name, ValueDeclaration pat body wheres) | name <- patNames' pat]
  go _ = []

lookupDefinition :: Name -> Environment -> Maybe Declarable
lookupDefinition = M.lookup

-- Find expression and in-scope environment at a path in an AST
envExpAt :: Environment -> Exp -> ExpKey -> Maybe (Environment, Exp)
envExpAt topEnv topExp startingKey =
  case go topEnv topExp startingKey of
    Left (env, exp) -> Just (env, exp)
    Right _ -> Nothing
  where
    go env exp key =
      let newEnv =
            case exp of
              LetE decs body -> addNewEnvs env $ defines <$> decs
              _ -> env
      in
      case key of
        [] -> Left (newEnv, exp)
        head:rest -> adjustRecursiveA (\exp -> go newEnv exp rest) [head] exp

type EvaluateM = ReaderT HaltHandlers (Except String)

data HaltHandlers = HaltHandlers
  { lookupVariable :: Name -> ExpKey -> LookupVariableResponse
  }

data LookupVariableResponse
  = LookupVariableFound Declarable
  | LookupVariableNotFound Environment Exp
  | LookupVariableNodeMissing
  deriving (Show)

data ReductionResultF a
  = CannotReduce { getRedRes :: a }
  | NewlyReduced { getRedRes :: a }
  deriving (Show, Functor)

isCannotReduce :: ReductionResultF a -> Bool
isCannotReduce (CannotReduce _) = True
isCannotReduce _ = False

type ReductionResult = ReductionResultF Exp

instance Applicative ReductionResultF where
  pure = NewlyReduced
  (<*>) (NewlyReduced f) (NewlyReduced a) = NewlyReduced $ f a
  (<*>) (CannotReduce f) a                = CannotReduce $ f $ getRedRes a
  (<*>) f                (CannotReduce a) = CannotReduce $ getRedRes f a

evaluate :: Environment -> Exp -> Either String ReductionResult
evaluate topEnv exp = runExcept $ runReaderT (reduce $ annKeys exp) haltHandlers
  where
    haltHandlers = HaltHandlers { lookupVariable }
    lookupVariable name expKey =
      case envExpAt topEnv exp expKey of
        Nothing -> LookupVariableNodeMissing
        Just (env, targetNode) ->
          case lookupDefinition name env of
            Nothing -> LookupVariableNotFound env targetNode
            Just definition -> LookupVariableFound definition

-- TODO: This let-pruning has a bug: may misorder replacements
-- e.g. let b = a; c = b in c => let c = b in c => b
letWrap :: [Dec] -> Exp -> Exp
letWrap decls e =
  let getSimplicity (ValD (VarP from) (NormalB (VarE to)) []) = Left (from, to)
      getSimplicity decl = Right decl

      (simpleDecls, complexDecls) = partitionEithers $ map getSimplicity decls

      applySimpleDecl :: (Name, Name) -> Exp -> Exp
      applySimpleDecl (from, to) exp = replaceName from to exp
  in
  case (simpleDecls, complexDecls) of
    ([], []) -> e
    ([], _) -> LetE complexDecls e
    (_, _) -> foldr applySimpleDecl (letWrap complexDecls e) simpleDecls

nameUsedIn :: Exp -> Name -> Bool
nameUsedIn exp name = name `elem` collectNames exp -- TODO: does not cover all uses, AT ALL (only checks Exp nodes)
  where
    collectNames :: Exp -> [Name]
    collectNames = fst . transformMutM @Exp @Name (\x -> ([x], x))

isDeclLivingIn :: Exp -> Dec -> Bool
isDeclLivingIn exp (FunD name _) = nameUsedIn exp name
isDeclLivingIn exp (ValD pat _ _) = any (nameUsedIn exp) (childrenBi pat)
isDeclLivingIn _ _ = error "isDeclLivingIn: Unrecognized pattern"

reduce :: Fix (RecKey Exp) -> EvaluateM ReductionResult
reduce exp = match (keyed expf)
  where
    Fix (Pair (Const path) expf) = exp

    modifySubExp :: (Fix (RecKey Exp) -> EvaluateM ReductionResult) -> ExpKey -> EvaluateM ReductionResult
    modifySubExp modifier path =
      getCompose $
        adjustRecursiveGGA
          (Compose . modifier)
          (\(Pair cann ffix) -> ffix)
          (\f k (Pair cann ffix) -> adjust f k ffix)
          path
          exp

    reduceSubExp :: ExpKey -> EvaluateM ReductionResult
    reduceSubExp = modifySubExp reduce

    replaceSubExp :: ExpKey -> Exp -> EvaluateM ReductionResult
    replaceSubExp key exp = modifySubExp (const $ pure $ NewlyReduced exp) key

    cannotReduce :: EvaluateM ReductionResult
    cannotReduce = pure $ CannotReduce $ deann exp

    lookupVar :: Name -> EvaluateM LookupVariableResponse
    lookupVar name = asks $ \h -> lookupVariable h name path

    match :: ExpF (Key ExpF, Fix (RecKey Exp)) -> EvaluateM ReductionResult

    -- can't reduce literals
    match (LitEF _) = cannotReduce

    -- remove let statements when appropriate
    match (LetEF decls (bodyIdx, body)) =
      let extractMatchingPat orig@(ValD pat (NormalB exp) _) -- TODO: handle guards
            | VarP _ <- pat
            = Left orig
            | Right matches <- matchPatKeyed pat exp
            = Right matches
          extractMatchingPat orig = Left orig

          matchingPats :: [Either Dec MatchSuccess]
          matchingPats = map extractMatchingPat decls
      in
      if any isRight matchingPats
      then do
        let explodedMatchingPats :: [Dec]
            explodedMatchingPats = concat $ either (:[]) (mapMaybe patExpPairToValDecl) <$> matchingPats
        replaceSubExp [] $ letWrap explodedMatchingPats (deann body)
      else
        -- TODO: circular definitions & other AST traversals, so we can remove one-at-a-time
        let remainingDecls = filter (isDeclLivingIn (deann body)) decls
        in
        if length remainingDecls < length decls
          then replaceSubExp [] $ letWrap remainingDecls (deann body)
          else reduceSubExp [bodyIdx]

    -- handle if statements
    match (CondEF (condIdx, cond) (_, true) (_, false)) =
      case matchPatKeyed (ConP 'True []) (deann cond) of
        Right _ -> replaceSubExp [] $ deann true
        Left (Mismatch _) -> replaceSubExp [] $ deann false
        Left (NeedsReduction (patKey, expKey)) ->
          reduceSubExp (condIdx : expKey)
        Left (UnexpectedErrorMatch _ _) ->
          throwError "CondE: Unexpected error in matching process - this should not happen!"

    -- handle case statements
    match (CaseEF (targetIdx, target) branches) =
      foldr handleBranch noBranchesLeft (zip [0..] branches)
      where
      noBranchesLeft = replaceSubExp [] $(lift =<< [e| error "Inexhaustive pattern match." |])
      handleBranch (ii, branch) tryNext
        = let Match pat matchBody decls = branch
              NormalB body = matchBody -- TODO: handle guards
              explodeIntoLet boundVars =
                letWrap (mapMaybe patExpPairToValDecl boundVars ++ decls) body
          in
          case matchPatKeyed pat (deann target) of
            Right boundVars ->
              replaceSubExp [] $ explodeIntoLet boundVars
            Left (Mismatch (patKey, expKey)) ->
              tryNext
            Left (NeedsReduction (patKey, expKey)) ->
              reduceSubExp (targetIdx : expKey)
            Left (UnexpectedErrorMatch _ _) ->
              error "Unexpected error in matching process - this should not happen!"

    match _
      -- handle function application
      | FlattenedApps { func, args, intermediateFuncs } <- flattenAppsKeyed (annKeys $ deann @Exp exp)
      , VarE name <- deann func
      = do
      declaration <- lookupVar name
      case declaration of
        -- TODO: handle failed lookup
        -- TODO: handle when looked-up var is not a function
        LookupVariableNodeMissing -> throwError $ "Couldn't find target node, this is a serious error, please contact." -- TODO: Classify error severity
        LookupVariableNotFound env target -> throwError $ "Couldn't find variable " ++ show name ++ "\n  at node: " ++ pprint target ++ "\n  in environment: " ++ show env
        LookupVariableFound (ValueDeclaration pat body wheres) -> -- TODO: handle lookup of a lambda (probably means an error in flattenApps)
          let Fix (Pair (Const funcIdx) _) = func
              NormalB bodyExp = body -- TODO: handle guards
              VarP name = pat -- TODO: when pat is not a variable, should somehow dispatch forcing of the lazy pattern declaration until it explodes into subexpressions
          in
          replaceSubExp funcIdx $ letWrap wheres bodyExp
        LookupVariableFound (DataField pat exp) ->
          throwError "reduce: Cannot handle data accessors yet"
        LookupVariableFound (FunctionDeclaration definition) ->
          let cardinality :: Int
              cardinality =
                case definition of
                  CustomFD cardinality _ -> cardinality
                  ClausesFD (Clause pats _ _:_) -> length pats -- function definitions should have at least one clause

              clauseToHandler :: Clause -> [Exp] -> Either (Int, MatchFailure) Exp
              clauseToHandler (Clause pats body wheres) args =
                let NormalB expBody = body -- TODO: Handle guards
                    clauseMatches = zip [0..] $ zipWith matchPatKeyed pats args
                    go [] = Right []
                    go ((_, Right matches):rest) = (matches ++) <$> go rest
                    go ((i, Left err):rest) = Left (i, err)
                in
                case go clauseMatches of
                  Left err -> Left err
                  Right bindings -> Right $ letWrap (mapMaybe patExpPairToValDecl bindings ++ wheres) expBody -- TODO: Do where decls take precedence over arguments?

              handlers :: [[Exp] -> Either (Int, MatchFailure) Exp]
              handlers =
                case definition of
                  CustomFD _ handler -> [unCustomShow handler]
                  ClausesFD clauses -> map clauseToHandler clauses

              headArgs, remainingArgs :: [Maybe Exp]
              headArgs = take cardinality $ map (fmap deann) args
              remainingArgs = drop cardinality $ map (fmap deann) args

              targetFunctionPath :: ExpKey
              (_, _, Fix (Pair (Const targetFunctionPath) _)) = getIntermediateFunc cardinality intermediateFuncs

              inexhaustivePatternMatch = replaceSubExp [] $(lift =<< [e| error "Inexhaustive pattern match in function " |]) -- TODO add function name to error
              runHandler (ii, handler) rest =
                case handler (fromJust <$> headArgs) of
                  Left (argIdx, NeedsReduction (_, argSubPath)) -> do
                    --emitLog $ show argIdx ++ "th argument needs further reduction"
                    let (Fix (Pair (Const path) _)) = map fromJust args !! argIdx
                    reduceSubExp (path ++ argSubPath) -- TODO: Do we need to handle CannotReduce?
                  Left (argIdx, Mismatch _) -> do
                    --emitLog $ show argIdx ++ "th clause did not match"
                    rest
                  -- TODO: Handle other kinds of failure
                  Right result ->
                    replaceSubExp targetFunctionPath result
          in
          if any isNothing headArgs
            then error "not fully applied!" -- TODO: Handle partial application
            else foldr runHandler inexhaustivePatternMatch (zip [0..] handlers)

      -- handle constructor application
      | FlattenedApps { func, args, intermediateFuncs } <- flattenAppsKeyed (annKeys $ deann @Exp exp)
      , ConE _ <- deann func
      = let tryArg (i, Nothing) rest = rest
            tryArg (i, Just (Fix (Pair (Const path) _))) rest = do
              reduction <- reduceSubExp path
              case reduction of
                CannotReduce _ -> rest
                NewlyReduced exp -> pure $ NewlyReduced exp
            finish = pure $ CannotReduce (deann exp)
        in
        foldr tryArg finish (zip [0..] args)
