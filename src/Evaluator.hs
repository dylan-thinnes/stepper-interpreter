{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
module Evaluator where

import "base" Control.Applicative
import "base" Control.Monad (zipWithM, ap)
import "base" Data.Bifunctor (first)
import "base" Data.Foldable (fold, toList)
import "base" Data.Function ((&))
import "base" Data.Functor.Compose
import "base" Data.Functor.Const
import "base" Data.Functor.Product
import "base" Data.Functor.Identity
import "base" Data.Either (isRight, partitionEithers)
import "base" Data.Maybe (isNothing, catMaybes, fromJust, mapMaybe)
import "base" Data.Void
import "base" Data.Data
import "base" Data.List
import "base" GHC.Generics

import qualified "containers" Data.Map as M
import           "containers" Data.Map (Map)

import "data-hash" Data.Hash qualified as Hash

import "data-fix" Data.Fix (Fix(..))

import "keys" Data.Key (Key(..), Keyed(..), keyed, Adjustable(..))

import "lens" Control.Lens qualified as L

import "mtl" Control.Monad.Reader hiding (lift)
import "mtl" Control.Monad.Except hiding (lift)

import "pretty" Text.PrettyPrint.Annotated (renderSpans)

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..), Name(..), NameFlavour(..), OccName(..))

import "transformers" Control.Monad.Trans.Maybe qualified as MT
import "transformers" Control.Monad.Trans.Class qualified as MT

import "uniplate" Data.Generics.Uniplate.Data

import "recursion-schemes" Data.Functor.Foldable qualified as R
import "recursion-schemes" Data.Functor.Foldable.TH qualified as R

import Lift
import Ppr qualified as P

import Debug.Trace

-- Utils

zipConcatM :: Monad m => (a -> b -> m [c]) -> [a] -> [b] -> m [c]
zipConcatM f as bs = concat <$> zipWithM f as bs

updateList :: (a -> a) -> Int -> [a] -> [a]
updateList f idx xs = map (\(i, x) -> if i == idx then f x else x) (zip [0..] xs)

removeList :: Int -> [a] -> [a]
removeList idx xs = concatMap (\(i, x) -> if i == idx then [] else [x]) (zip [0..] xs)

hoistMT :: Applicative m => Maybe a -> MT.MaybeT m a
hoistMT = MT.MaybeT . pure

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
  = Mismatch (PatKey, ExpDeepKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | NeedsReduction (PatKey, ExpDeepKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | UnexpectedErrorMatch String (PatKey, ExpDeepKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch
  deriving (Show, Lift)

type MatchSuccess = [(Pat, ExpWithDeepKey)]
type MatchSuccess' = [(Pat, Exp)]
type MatchMonad a = Either MatchFailure a
type MatchResult = MatchMonad MatchSuccess
type MatchResult' = MatchMonad MatchSuccess'

matchPat :: Pat -> Exp -> MatchResult
matchPat = matchPatConfigurable False

matchPatConfigurable :: Bool -> Pat -> Exp -> MatchResult
matchPatConfigurable goThroughLet pat exp = matchPatKeyedConfigurable goThroughLet (annKeys pat) (annDeepKeys [] exp)

matchPatKeyed :: RecKey Pat -> ExpWithDeepKey -> MatchResult
matchPatKeyed = matchPatKeyedConfigurable False

matchPatKeyedConfigurable :: Bool -> RecKey Pat -> ExpWithDeepKey -> MatchResult
matchPatKeyedConfigurable goThroughLet = go
  where
    go :: RecKey Pat -> ExpWithDeepKey -> MatchResult
    go annPat annExp = matchLists annPat annExp
      where
      (patKey, patFAnn) = toKeyPair annPat
      (expKey, expFAnn) = toKeyPair annExp

      mismatch, needsReduction :: MatchMonad a
      mismatch = Left $ Mismatch (patKey, expKey)
      needsReduction = Left $ NeedsReduction (patKey, expKey)

      unexpectedError :: String -> MatchMonad a
      unexpectedError msg = Left $ UnexpectedErrorMatch msg (patKey, expKey)

      matchLists :: RecKey Pat -> ExpWithDeepKey -> MatchResult
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
          _ -> match expKey patFAnn expFAnn

      match :: ExpDeepKey -> PatF (RecKey Pat) -> ExpF ExpWithDeepKey -> MatchResult
      match _ (LitPF pat) (LitEF exp)
        | pat == exp = Right []
        | otherwise = mismatch
      match deepKey (VarPF name) exp = Right [(VarP name, annOne deepKey exp)]
      match _ (TupPF pats) (TupEF mexps)
        | length pats /= length mexps = unexpectedError "Tuple pattern-expression arity mismatch."
        | otherwise = do
            -- If there are any Nothing expressions, the tuple expression is partially applied and we short circuit with an error
            let onlyJust :: Maybe a -> MatchMonad a
                onlyJust Nothing = unexpectedError "Tuple expression is not fully applied (e.g. is a partially applied tuple like (,,) or (1,))."
                onlyJust (Just a) = pure a
            exps <- traverse onlyJust mexps
            zipConcatM go pats exps
      match _ (UnboxedTupPF _) _ = error "matchPatKeyed: Unsupported UnboxedTupP pattern in AST"
      match _ (UnboxedSumPF _ _ _) _ = error "matchPatKeyed: Unsupported UnboxedSumP pattern in AST"
      match _ (ConPF patConName pats) _
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
      match _ (InfixPF patL patConName patR) _
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
      match _ (UInfixPF patL _ patR) _ = error "matchPatKeyed: Unsupported pat UInfixP"
      match _ (ParensPF pat) exp = go pat annExp
      match _ pat (ParensEF exp) = go annPat exp
      match deepKey (TildePF pat) exp = Right [(deann pat, annOne deepKey exp)] -- lazy patterns always match, deferred to a "let-desugaring"
      match _ (BangPF pat) exp = error "matchPatKeyed: Unsupported pat BangP"
      match deepKey (AsPF name pat) exp = do
        submatches <- go pat annExp
        pure $ (VarP name, annOne deepKey exp) : submatches
      match _ WildPF _ = Right []
      match _ (RecPF _ fieldPats) _ = error "matchPatKeyed: Unsupported pat RecP" -- TODO: Urgently need to support field patterns
      match _ (ListPF pats) (ListEF exps) -- TODO: handle conses <=> list literals
        | length pats /= length exps = unexpectedError "List pattern and list expression have different lengths."
        | otherwise = zipConcatM go pats exps
      match _ (SigPF pat type_) _ = error "matchPatKeyed: Unsupported pat SigP"
      match _ (ViewPF exp pat) _ = error "matchPatKeyed: Unsupported pat ViewP"

      -- TODO: How does matching through lets & other scope-affecting nodes work? Must consider.
      -- Ans: It messes with matching CONSIDERABLY, added flag to enable it in demos
      match _ pat (LetEF _ exp) | goThroughLet = go annPat exp

      match _ pat exp
        -- TODO: Definitely unfinished cases here somewhere...
        | FlattenedApps { func } <- flattenAppsKeyed annExp
        , (ConE _) <- deann func
        = mismatch
        | (ConP _ _) <- deann annPat -- May be too aggressive...
        = needsReduction
        | otherwise
        = needsReduction -- TODO: Consider how caller checks for forcing of an `error "msg"`

patDeepExpPairToValDecl :: (Pat, ExpWithDeepKey) -> Maybe Dec
patDeepExpPairToValDecl (pat, exp) = patExpPairToValDecl (pat, deann exp)

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

getIntermediateFunc :: Show a => Int -> [(Int, a)] -> (Int, Int, a)
getIntermediateFunc origN origXs = go origN origXs
  where
    go n [] = error $ "getIntermediateFunc: ran out of functions, " ++ show origN ++ ", " ++ show (length origXs) ++ ", " ++ show origXs
    go n ((size, f):rest)
      | n <= size = (n, size, f)
      | otherwise = go (n - size) rest

flattenAppsF :: (a, ExpF a) -> Maybe (FlattenedApps a)
flattenAppsF (orig, AppEF func arg) = Just $ FlattenedApps func [Just arg] [(1, orig)]
flattenAppsF (orig, InfixEF mlarg func mrarg) = Just $ FlattenedApps func [mlarg, mrarg] [(2, orig)]
flattenAppsF _ = Nothing

flattenApps :: Exp -> FlattenedApps Exp
flattenApps = flattenAppsG id

flattenAppsKeyed :: With Exp a -> FlattenedApps (With Exp a)
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

expToIsListKeyed :: With Exp a -> IsList (With Exp a)
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

patToIsListKeyed :: RecKey Pat -> IsList (RecKey Pat)
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
  | ValueDeclaration (Maybe (ExpDeepKey, Int)) Pat Body [Dec] -- let <pat> = <body> where <...decs>
  | DataField Pat Name -- field for a datatype, e.g. MyDatatype { myField :: Int }
  | Seq
  deriving (Show)

debugDeclarable :: Declarable -> String
debugDeclarable (FunctionDeclaration funDecl) = debugFunctionDeclaration funDecl
debugDeclarable (ValueDeclaration location pat body decs) = "Value: " ++ pprint (ValD pat body decs)
debugDeclarable (DataField pat name) = concat ["DataField: field \"", pprint name, "\" in ", pprint pat]
debugDeclarable Seq = "Seq: Seq"

data FunctionDeclaration
  = ClausesFD [Clause]
  | CustomFD Int (CustomShow ([Exp] -> Either (Int, MatchFailure) Exp))
    -- "escape hatch" for functions w/ strict cardinality, like (+), can force reduction of nth argument
    -- TODO: Implement full MatchResult generality for CustomFD
  deriving (Show)

data CustomShow a = CustomShow { msg :: String, unCustomShow :: a }
instance Show (CustomShow a) where
  show (CustomShow msg _) = msg

debugFunctionDeclaration :: FunctionDeclaration -> String
debugFunctionDeclaration (ClausesFD clauses) = unlines ("Clauses Func: " : map (\clause -> "  " ++ pprint clause) clauses)
debugFunctionDeclaration (CustomFD arity func) = concat ["Custom Func: ", show func, ", arity: ", show arity]

-- TODO: Deal with environment clobbering names that are used repeatedly, i.e. let a = 1 in let a = a + 4 in a
type Environment = Map EnvName Declarable

data EnvName = RawName String | FullName Name
  deriving (Show, Eq, Ord)

nameToFullAndRaw :: Name -> (EnvName, EnvName)
nameToFullAndRaw fullName@(Name (OccName rawName) _) = (FullName fullName, RawName rawName)

defaultEnvironment :: Environment
defaultEnvironment = mkEnvironment [('(+), plus), ('(*), times), ('seq, Seq)]
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
mkEnvironment = M.fromList . concatMap toRawFull
  where
    toRawFull (name, declarable) =
      let (fullName, rawName) = nameToFullAndRaw name
      in
      [(fullName, declarable)
      ,(rawName, declarable)
      ]

debugEnvironment :: Environment -> String
debugEnvironment env = unlines $ map showKV $ M.toList env
  where
    showKV (key, value) = concat ["Name: ", show key, ", declaration: ", debugDeclarable value]

addNewEnvs :: Environment -> [Environment] -> Environment
addNewEnvs env news = foldl updateEnv env news
  where
    updateEnv :: Environment -> Environment -> Environment
    updateEnv env new = M.unionWith const new env

defines :: Maybe (ExpDeepKey, Int) -> Dec -> Environment
defines location dec = mkEnvironment $ do
  declarable <- defines' dec
  case declarable of
    (name, ValueDeclaration _ pat body wheres) ->
      pure (name, ValueDeclaration location pat body wheres)
    declarable -> pure declarable

defines' :: Dec -> [(Name, Declarable)]
defines' = go
  where
  targetName = $(lift =<< newName "target")

  go (FunD name clauses) = [(name, FunctionDeclaration $ ClausesFD clauses)]
  go (ValD pat body wheres) = [(name, ValueDeclaration Nothing pat body wheres) | name <- patNames' pat]
  go (DataD ctx name tyvars kind cons derivs) = concatMap definesCon cons
    where
      mkDataField size conName idx var =
        let extractor =
              ConP conName $ updateList (const (VarP targetName)) idx (replicate size WildP)
        in
        (var, DataField extractor targetName)
      definesCon (RecC name varBangs) = do
        (idx, (var, _, _)) <- zip [0..] varBangs
        pure $ mkDataField (length varBangs) name idx var
      definesCon (RecGadtC names varBangs finalType) = do
        name <- names
        (idx, (var, _, _)) <- zip [0..] varBangs
        pure $ mkDataField (length varBangs) name idx var
      definesCon _ = []
  go _ = []

lookupDefinition :: Name -> Environment -> Maybe Declarable
lookupDefinition name env =
  let (fullName, rawName) = nameToFullAndRaw name
  in
  case (lookupDefinitionFullRaw fullName env, lookupDefinitionFullRaw rawName env) of
    (Just decl, _) -> Just decl
    (_, Just decl) -> Just decl
    _ -> Nothing

lookupDefinitionFullRaw :: EnvName -> Environment -> Maybe Declarable
lookupDefinitionFullRaw = M.lookup

lookupDefinitionFullOnly :: Name -> Environment -> Maybe Declarable
lookupDefinitionFullOnly name = lookupDefinitionFullRaw (FullName name)

lookupDefinitionRaw :: String -> Environment -> Maybe Declarable
lookupDefinitionRaw raw = lookupDefinitionFullRaw (RawName raw)

envFromDecs :: [Dec] -> Environment
envFromDecs decs = addNewEnvs defaultEnvironment (map (defines Nothing) decs)

-- Find expression and in-scope environment at a path in an AST
envExpAt :: Environment -> Exp -> ExpDeepKey -> Maybe (Environment, Exp)
envExpAt topEnv topExp startingKey =
  case go topEnv topExp startingKey of
    Left (env, exp) -> Just (env, exp)
    Right _ -> Nothing
  where
    go :: Environment -> Exp -> ExpDeepKey -> Either (Environment, Exp) Exp
    go env exp key =
      let newEnv :: Environment
          newEnv =
            case exp of
              LetE decs body -> addNewEnvs env $ zipWith (\i -> defines (Just (key, i))) [0..] decs
              _ -> env
      in
      case key of
        [] -> Left (newEnv, exp)
        (head:rest) -> modExpByDeepKeyA [head] (\exp -> go newEnv exp rest) exp

type EvaluateM = ReaderT EvaluationInfo (Except String)

data EvaluationInfo = EvaluationInfo
  { _lookupVariable :: Name -> ExpDeepKey -> LookupVariableResponse
  , _reduce :: ExpDeepKey -> EvaluateM ReductionResult
  , _replace :: Maybe String -> ExpDeepKey -> Exp -> EvaluateM ReductionResult
  , _makeUniqueName :: ExpDeepKey -> Name -> Name
  }

lookupVariableAbsolute :: Name -> ExpDeepKey -> EvaluateM LookupVariableResponse
lookupVariableAbsolute name path = asks $ \f -> _lookupVariable f name path

reduceAbsolute :: ExpDeepKey -> EvaluateM ReductionResult
reduceAbsolute path = ask >>= \f -> _reduce f path

replaceAbsolute :: Maybe String -> ExpDeepKey -> Exp -> EvaluateM ReductionResult
replaceAbsolute reason path exp = ask >>= \f -> _replace f reason path exp

makeUniqueNameAbsolute :: ExpDeepKey -> Name -> EvaluateM Name
makeUniqueNameAbsolute path name = asks $ \f -> _makeUniqueName f path name

makeUniqueNamesAbsolute :: (Data from, Biplate from Name) => ExpDeepKey -> from -> EvaluateM from
makeUniqueNamesAbsolute path = transformBiM (makeUniqueNameAbsolute path)

data LookupVariableResponse
  = LookupVariableFound Declarable
  | LookupVariableNotFound Environment Exp
  | LookupVariableNodeMissing
  deriving (Show)

data ReductionResultF a
  = CannotReduce { getRedRes :: a }
  | NewlyReduced { reason :: Maybe String, getRedRes :: a }
  deriving (Show, Functor)

isCannotReduce :: ReductionResultF a -> Bool
isCannotReduce (CannotReduce _) = True
isCannotReduce _ = False

type ReductionResult = ReductionResultF Exp

instance Applicative ReductionResultF where
  pure = NewlyReduced Nothing
  (<*>) (NewlyReduced r1 f) (NewlyReduced r2 a) = NewlyReduced (r1 <> r2) $ f a
  (<*>) (CannotReduce f)    a                   = CannotReduce $ f $ getRedRes a
  (<*>) f                   (CannotReduce a)    = CannotReduce $ getRedRes f a

evaluate :: Environment -> Exp -> Either String ReductionResult
evaluate topEnv topExp = runExcept $ runReaderT (reduce annotated) haltHandlers
  where
    annotated = annDeepKeys [] topExp

    haltHandlers =
      EvaluationInfo {
        _lookupVariable,
        _reduce,
        _replace,
        _makeUniqueName
      }

    _reduce :: ExpDeepKey -> EvaluateM ReductionResult
    _reduce key =
      case modAnnExpByDeepKeyA key Left annotated of
        Left targetNode -> reduce targetNode
        Right _ -> throwError $ "Error: Couldn't find index: " ++ show key

    modifyExp :: (ExpWithDeepKey -> EvaluateM ReductionResult) -> ExpDeepKey -> EvaluateM ReductionResult
    modifyExp modifier path =
      let composedModifier :: ExpWithDeepKey -> Compose EvaluateM ReductionResultF ExpWithDeepKey
          composedModifier expWDK@(Fix (Pair (Const deepKey) _)) = fmap (annDeepKeys deepKey) $ Compose $ modifier expWDK
      in
      getCompose $ fmap deann $ modAnnExpByDeepKeyA path composedModifier annotated

    _replace :: Maybe String -> ExpDeepKey -> Exp -> EvaluateM ReductionResult
    _replace reason key exp = modifyExp (const $ pure $ NewlyReduced reason exp) key

    _lookupVariable :: Name -> ExpDeepKey -> LookupVariableResponse
    _lookupVariable name expKey =
      case envExpAt topEnv topExp expKey of
        Nothing -> LookupVariableNodeMissing
        Just (env, targetNode) ->
          case lookupDefinition name env of
            Nothing -> LookupVariableNotFound env targetNode
            Just definition -> LookupVariableFound definition

    _makeUniqueName :: ExpDeepKey -> Name -> Name
    _makeUniqueName expKey name =
      case envExpAt topEnv topExp expKey of
        Nothing -> name
        Just (env, targetNode) ->
          let hashName :: Name -> Name
              hashName (Name occ flav) = Name (incrementName occ) (hashFlavour flav)

              hashUntilUnique :: Name -> Name
              hashUntilUnique name =
                case lookupDefinitionFullOnly name env of
                  Nothing -> name
                  Just _ -> hashUntilUnique $ hashName name
          in
          hashUntilUnique name

hashFlavour :: NameFlavour -> NameFlavour
hashFlavour flavour = case flavour of
  NameU uniq -> NameU $ fromIntegral $ Hash.asWord64 $ Hash.hash uniq
  NameL uniq -> NameL $ fromIntegral $ Hash.asWord64 $ Hash.hash uniq
  flav -> flav

incrementName :: OccName -> OccName
incrementName (OccName occ) = OccName modified
  where
  beforeUS = takeWhile (/= '_') occ
  afterUS = drop (length beforeUS + 1) occ
  modified =
    case reads @Int afterUS of
      [(i, "")] -> beforeUS ++ "_" ++ show (i + 1)
      _ -> beforeUS ++ "_0"

-- TODO: This let-pruning has a bug: may misorder replacements
-- e.g. let b = a; c = b in c => let c = b in c => b
data SimpleDecl = VarRename Name Name | FullyReduced Name Exp

isSimpleDecl :: Dec -> Maybe SimpleDecl
isSimpleDecl (ValD (VarP from) (NormalB body) [])
  | Just to <- getVarExp body
  = Just $ VarRename from to
  | fullyReduced body
  = Just $ FullyReduced from body -- TODO: How much do we want to actually substitute?
    where
      fullyReduced exp
        | LitE _ <- exp
        = True
        | FlattenedApps { func = ConE _, args } <- flattenApps exp
        = all (maybe True fullyReduced) args
        | NotList <- expToIsList exp
        = False
        | otherwise
        = True
isSimpleDecl _ = Nothing

partitionSimpleDecls :: [Dec] -> ([(SimpleDecl, Dec)], [Dec])
partitionSimpleDecls = partitionEithers . map eitherSimpleDecl
  where
    eitherSimpleDecl :: Dec -> Either (SimpleDecl, Dec) Dec
    eitherSimpleDecl decl =
      case isSimpleDecl decl of
        Just simpleDecl -> Left (simpleDecl, decl)
        Nothing -> Right decl

applySimpleDecl :: SimpleDecl -> Exp -> Exp
applySimpleDecl (VarRename from to) exp = replaceName from to exp
applySimpleDecl (FullyReduced from to) exp = replaceName' from to exp

letWrap :: [Dec] -> Exp -> Exp
letWrap [] exp = exp
letWrap decls exp = LetE decls exp

nameUsedIn :: forall from. (Data from, Biplate from Name) => from -> Name -> Bool
nameUsedIn exp name = name `elem` collectNames @from exp

collectNames :: forall from. (Data from, Biplate from Name) => from -> [Name]
collectNames = fst . transformBiM @_ @from @Name (\x -> ([x], x))

isDeclLivingIn :: forall from. (Data from, Biplate from Name) => from -> Dec -> Bool
isDeclLivingIn exp (FunD name _) = nameUsedIn exp name
isDeclLivingIn exp (ValD pat _ _) = any (nameUsedIn exp) (childrenBi pat)
isDeclLivingIn _ _ = error "isDeclLivingIn: Unrecognized pattern"

getVarExp :: Exp -> Maybe Name
getVarExp (VarE name) = Just name
getVarExp (UnboundVarE name) = Just name
getVarExp _ = Nothing

whnf :: Exp -> Bool
whnf exp
  | LitE _ <- exp
  = True
  | FlattenedApps { func = ConE _ } <- flattenApps exp
  = True
  | NotList <- expToIsList exp
  = False
  | otherwise
  = True

reduce :: ExpWithDeepKey -> EvaluateM ReductionResult
reduce exp = match
  where
    Fix (Pair (Const globalPath) expf) = exp

    cannotReduce :: EvaluateM ReductionResult
    cannotReduce = pure $ CannotReduce $ deann exp

    replaceSelf :: Maybe String -> Exp -> EvaluateM ReductionResult
    replaceSelf reason = replaceRelative reason []

    replaceRelative :: Maybe String -> ExpDeepKey -> Exp -> EvaluateM ReductionResult
    replaceRelative reason path = replaceAbsolute reason (globalPath ++ path)

    reduceRelative :: ExpDeepKey -> EvaluateM ReductionResult
    reduceRelative path = reduceAbsolute (globalPath ++ path)

    lookupVariable :: Name -> EvaluateM LookupVariableResponse
    lookupVariable name = do
      lookupVariableAbsolute name globalPath

    makeUniqueName :: Name -> EvaluateM Name
    makeUniqueName name = makeUniqueNameAbsolute globalPath name

    forcesViaCase :: Exp -> Maybe ExpKey
    forcesViaCase exp =
      case projectK exp of
        CaseEF (targetIdx, target) _ -> Just [targetIdx]
        CondEF (targetIdx, target) _ _ -> Just [targetIdx]
        _ -> Nothing

    match :: EvaluateM ReductionResult
    match = do
      alternatives <- sequence
        [ MT.runMaybeT matchForcesViaCase
        , sequence matchLiterals
        , sequence matchLet
        , sequence matchCond
        , sequence matchCase
        , MT.runMaybeT matchFunctionApplication
        ]
      case foldr (<|>) empty alternatives of
        Just result -> pure result
        Nothing -> error noMatchMsg
      where
        noMatchMsg :: String
        noMatchMsg = "reduce: Can't match " ++ pprint (deann @Exp exp) ++ ", AST: " ++ show (deann @Exp exp)

    matchForcesViaCase :: MT.MaybeT EvaluateM ReductionResult
    matchForcesViaCase = do
      Just targetPath <- pure $ forcesViaCase (deann exp)
      -- deepTargetPath <- MT.lift $ getDeepKey targetPath
      Just (env, subexp) <- pure $ envExpAt defaultEnvironment (deann exp) (appendShallow globalPath targetPath)
      LetE decs body <- pure subexp
      MT.lift $ replaceSelf Nothing $ letWrap decs $ modExpByKey targetPath (const body) (deann exp)

    -- can't reduce literals
    matchLiterals
      | LitEF _ <- expf
      = Just cannotReduce
      | otherwise
      = empty

    -- modify let statements when appropriate
    matchLet
      | LetEF decls (bodyIdx, body) <- keyed expf
      = Just
      $ if
          | let extractMatchingPat orig@(ValD pat (NormalB exp) _) -- TODO: handle guards
                  | VarP _ <- pat
                  = Left orig
                  | Right matches <- matchPat pat exp
                  = Right matches
                extractMatchingPat orig = Left orig

                matchingPats :: [Either Dec MatchSuccess]
                matchingPats = map extractMatchingPat decls
          , any isRight matchingPats
          -> let explodedMatchingPats :: [Dec]
                 explodedMatchingPats =
                   concat $ either (:[]) (mapMaybe patDeepExpPairToValDecl) <$> matchingPats
             in
             replaceSelf Nothing $ letWrap explodedMatchingPats (deann body)
          | LetEF decls (bodyIdx, body) <- keyed expf
          , let remainingDecls :: [Dec]
                remainingDecls = map snd $ filter isDeclLiving $ zip [0..] decls

                isDeclLiving :: (Int, Dec) -> Bool
                isDeclLiving (idx, decl) =
                  let livesInBody = isDeclLivingIn (deann @Exp body) decl
                      nonSelfDecls = removeList idx decls
                      livesInOtherDecls = any (isDeclInDec decl) nonSelfDecls
                  in
                  livesInBody || livesInOtherDecls

                isDeclInDec :: Dec -> Dec -> Bool
                isDeclInDec decl (ValD _ body decs) = isDeclLivingIn body decl || any (`isDeclLivingIn` decl) decs
                isDeclInDec decl (FunD _ clauses) = any (`isDeclLivingIn` decl) clauses
                isDeclInDec decl _ = False
          , length remainingDecls < length decls
          -> replaceSelf Nothing $ letWrap remainingDecls (deann body)
          | (simpleDecl:rest, complexDecls) <- partitionSimpleDecls decls
          -> replaceSelf (Just "Simplify simple decl") $ letWrap (map snd rest ++ complexDecls) (applySimpleDecl (fst simpleDecl) (deann body))
          | otherwise
          -> reduceRelative [Right bodyIdx]
      | otherwise
      = empty

    -- handle if statements
    matchCond
      | (CondEF (condIdx, cond) (_, true) (_, false)) <- keyed expf
      = Just
      $ case matchPat (ConP 'True []) (deann cond) of
          Right _ -> replaceSelf Nothing $ deann true
          Left (Mismatch _) -> replaceSelf Nothing $ deann false
          Left (NeedsReduction (patKey, expKey)) ->
            reduceRelative (Right condIdx : expKey)
          Left (UnexpectedErrorMatch _ _) ->
            throwError "CondE: Unexpected error in matching process - this should not happen!"
      | otherwise
      = empty

    -- handle case statements
    matchCase
      | (CaseEF (targetIdx, target) branches) <- keyed expf
      = Just
      $ let
          noBranchesLeft = replaceSelf Nothing $(lift =<< [e| error "Inexhaustive pattern match." |])
          handleBranch (ii, branch) tryNext
            = let Match pat matchBody decls = branch
                  NormalB body = matchBody -- TODO: handle guards
                  explodeIntoLet boundVars =
                    letWrap (mapMaybe patExpPairToValDecl boundVars ++ decls) body
              in
              case matchPat pat (deann target) of
                Right boundVars ->
                  replaceSelf Nothing $ explodeIntoLet (map (fmap deann) boundVars)
                Left (Mismatch (patKey, expKey)) ->
                  tryNext
                Left (NeedsReduction (patKey, expKey)) ->
                  reduceRelative (Right targetIdx : expKey)
                Left (UnexpectedErrorMatch _ _) ->
                  error "Unexpected error in matching process - this should not happen!"
        in
        foldr handleBranch noBranchesLeft (zip [0..] branches)
      | otherwise
      = empty

    -- handle function application
    matchFunctionApplication = do
      FlattenedApps { func, args, intermediateFuncs } <- pure $ flattenAppsKeyed (annDeepKeys [] $ deann @Exp exp)
      if
        | Just name <- getVarExp $ deann func
        -> do
          declaration <- MT.lift $ lookupVariable name
          case declaration of
            -- TODO: handle failed lookup
            -- TODO: handle when looked-up var is not a function
            LookupVariableNodeMissing -> MT.lift $ throwError $ "Couldn't find target node, this is a serious error, please contact." -- TODO: Classify error severity
            LookupVariableNotFound env target -> MT.lift $ throwError $ "Couldn't find variable " ++ show name ++ "\n  at node: " ++ pprint target ++ "\n  rep: " ++ show target ++ "\n  in environment: " ++ debugEnvironment env
            LookupVariableFound (ValueDeclaration location pat body wheres)
              -- TODO: handle lookup of a lambda (probably means an error in flattenApps)
              | Fix (Pair (Const funcIdx) _) <- func
              , NormalB bodyExp <- body -- TODO: handle guards
              , VarP name <- pat -- TODO: when pat is not a variable, should somehow dispatch forcing of the lazy pattern declaration until it explodes into subexpressions
              -> MT.lift $ replaceRelative Nothing funcIdx $ letWrap wheres bodyExp
            LookupVariableFound (DataField pat name) -> MT.lift $
              let cardinality :: Int
                  cardinality = 1

                  clauseToHandler :: Clause -> [Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess)
                  clauseToHandler (Clause pats body wheres) args =
                    let NormalB expBody = body -- TODO: Handle guards
                        clauseMatches = zip [0..] $ zipWith matchPat pats args
                        go [] = Right []
                        go ((_, Right matches):rest) = (matches ++) <$> go rest
                        go ((i, Left err):rest) = Left (i, err)
                    in
                    case go clauseMatches of
                      Left err -> Left err
                      Right bindings -> Right (expBody, wheres, bindings)

                  singleClause :: Clause
                  singleClause = Clause [pat] (NormalB $ VarE name) []

                  handlers :: [[Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess)]
                  handlers = [clauseToHandler singleClause]

                  headArgs, remainingArgs :: [Maybe Exp]
                  headArgs = take cardinality $ map (fmap deann) args
                  remainingArgs = drop cardinality $ map (fmap deann) args

                  targetFunctionPath :: ExpDeepKey
                  (_, _, Fix (Pair (Const targetFunctionPath) _)) = getIntermediateFunc cardinality intermediateFuncs

                  inexhaustivePatternMatch :: EvaluateM ReductionResult
                  inexhaustivePatternMatch = replaceSelf Nothing $(lift =<< [e| error "Inexhaustive pattern match in function " |]) -- TODO add data constructor name to errors

                  runHandler
                    :: (Int, [Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess))
                    -> EvaluateM ReductionResult
                    -> EvaluateM ReductionResult
                  runHandler (ii, handler) rest =
                    case handler (fromJust <$> headArgs) of
                      Left (argIdx, NeedsReduction (_, argSubPath)) -> do
                        --emitLog $ show argIdx ++ "th argument needs further reduction"
                        let (Fix (Pair (Const path) _)) = map fromJust args !! argIdx
                        reduceRelative (path ++ argSubPath) -- TODO: Do we need to handle CannotReduce?
                      Left (argIdx, Mismatch _) -> do
                        --emitLog $ show argIdx ++ "th clause did not match"
                        rest
                      -- TODO: Handle other kinds of failure
                      Right (expression, wheres, bindings) -> do
                        let boundNames = concatMap (collectNames . fst) bindings
                        let toUnique name = if name `elem` boundNames then makeUniqueName name else pure name

                        -- warning: undecipherable lens magic:
                        uniqueBindings <- bindings & L.traverse . L._1 L.%%~ transformBiM toUnique
                        uniqueExpression <- transformBiM toUnique expression
                        uniqueWheres <- traverse (transformBiM toUnique) wheres

                        let result = letWrap (mapMaybe patDeepExpPairToValDecl uniqueBindings ++ uniqueWheres) uniqueExpression
                        replaceAbsolute Nothing targetFunctionPath result
              in
              if any isNothing headArgs
                then error "not fully applied!" -- TODO: Handle partial application
                else foldr runHandler inexhaustivePatternMatch (zip [0..] handlers)
            LookupVariableFound (FunctionDeclaration definition) -> MT.lift $
              let cardinality :: Int
                  cardinality =
                    case definition of
                      CustomFD cardinality _ -> cardinality
                      ClausesFD (Clause pats _ _:_) -> length pats -- function definitions should have at least one clause

                  clauseToHandler :: Clause -> [Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess)
                  clauseToHandler (Clause pats body wheres) args =
                    let NormalB expBody = body -- TODO: Handle guards
                        clauseMatches = zip [0..] $ zipWith matchPat pats args
                        go [] = Right []
                        go ((_, Right matches):rest) = (matches ++) <$> go rest
                        go ((i, Left err):rest) = Left (i, err)
                    in
                    case go clauseMatches of
                      Left err -> Left err
                      Right bindings -> Right (expBody, wheres, bindings)

                  handlers :: [[Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess)]
                  handlers =
                    case definition of
                      CustomFD _ handler -> [(fmap . fmap) (,[],[]) (unCustomShow handler)]
                      ClausesFD clauses -> map clauseToHandler clauses

                  headArgs, remainingArgs :: [Maybe Exp]
                  headArgs = take cardinality $ map (fmap deann) args
                  remainingArgs = drop cardinality $ map (fmap deann) args

                  targetFunctionPath :: ExpDeepKey
                  (_, _, Fix (Pair (Const targetFunctionPath) _)) = getIntermediateFunc cardinality intermediateFuncs

                  inexhaustivePatternMatch :: EvaluateM ReductionResult
                  inexhaustivePatternMatch = replaceSelf Nothing $(lift =<< [e| error "Inexhaustive pattern match in function " |]) -- TODO add function name to error

                  runHandler
                    :: (Int, [Exp] -> Either (Int, MatchFailure) (Exp, [Dec], MatchSuccess))
                    -> EvaluateM ReductionResult
                    -> EvaluateM ReductionResult
                  runHandler (ii, handler) tryRest =
                    case handler (fromJust <$> headArgs) of
                      Left (argIdx, NeedsReduction (_, argSubPath)) -> do
                        --emitLog $ show argIdx ++ "th argument needs further reduction"
                        let (Fix (Pair (Const path) _)) = map fromJust args !! argIdx
                        reduceRelative (path ++ argSubPath) -- TODO: Do we need to handle CannotReduce?
                      Left (argIdx, Mismatch _) -> do
                        --emitLog $ show argIdx ++ "th clause did not match"
                        tryRest
                      -- TODO: Handle other kinds of failure
                      Right (expression, wheres, bindings) -> do
                        let boundNames = concatMap (collectNames . fst) bindings
                        let toUnique name = if name `elem` boundNames then makeUniqueName name else pure name

                        -- warning: undecipherable lens magic:
                        uniqueBindings <- bindings & L.traverse . L._1 L.%%~ transformBiM toUnique
                        uniqueExpression <- transformBiM toUnique expression
                        uniqueWheres <- traverse (transformBiM toUnique) wheres

                        let result = letWrap (mapMaybe patDeepExpPairToValDecl uniqueBindings ++ uniqueWheres) uniqueExpression
                        replaceAbsolute Nothing targetFunctionPath result
              in
              if any isNothing headArgs
                then error "not fully applied!" -- TODO: Handle partial application
                else foldr runHandler inexhaustivePatternMatch (zip [0..] handlers)

            LookupVariableFound Seq -> MT.lift $
              let arg1, arg2 :: Maybe Exp
                  (arg1:arg2:_) = map (fmap deann) args

                  targetFunctionPath :: ExpDeepKey
                  (_, _, Fix (Pair (Const targetFunctionPath) _)) = getIntermediateFunc 2 intermediateFuncs
              in
              case (arg1, arg2) of
                (Just arg1, Just arg2) ->
                  if whnf arg1
                     then replaceRelative Nothing targetFunctionPath arg2 -- TODO: Implement seq!
                     else replaceRelative Nothing targetFunctionPath arg2
                _ -> error "not fully applied!" -- TODO: Handle partial application

            _ -> hoistMT Nothing
        | ConE _ <- deann func
        -> MT.lift
        $ let tryArg (i, Nothing) rest = rest
              tryArg (i, Just (Fix (Pair (Const path) _))) rest = do
                reduction <- reduceRelative path
                case reduction of
                  CannotReduce _ -> rest
                  NewlyReduced _ exp -> pure reduction
              finish = pure $ CannotReduce (deann exp)
          in
          foldr tryArg finish (zip [0..] args)
        | otherwise
        -> hoistMT empty

  {-
data MatchFailure
  = Mismatch (PatKey, ExpKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | NeedsReduction (PatKey, ExpKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | UnexpectedErrorMatch String (PatKey, ExpKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch
  deriving (Show, Lift)

type MatchSuccess = [(Pat, Exp)]
type MatchMonad a = Either MatchFailure a
type MatchResult = MatchMonad MatchSuccess
  -}

type ReferenceMatchSuccess = [(Pat, Exp)]

data ReferenceMatchFailure
  = RMNeedsReduction (PatKey, ExpKey) -- Specific subexpression needs further reduction due to given subpattern before pattern can be determined to match or fail
  | RMMismatch (PatKey, ExpKey) -- Pattern & expression both in WHNF and do not match - this pattern fails
  | RMUnexpectedErrorMatch String (PatKey, ExpKey) -- For errors that shouldn't occur if the type-system is checking, e.g. tuple arity mismatch
  | RMVariableHasPattern (ExpKey, Int)
  | RMVariableHasGuards (ExpKey, Int)
  | RMVariableNeedsReduction (ExpKey, Int) PatKey ExpKey
  | RMIndexingError String
  deriving (Show)

  {-
matchFailureToRefMatchFailure :: ExpDeepKey -> MatchFailure -> ReferenceMatchFailure
matchFailureToRefMatchFailure superPath (NeedsReduction (patKey, expKey)) = RMNeedsReduction (patKey, expKey)
matchFailureToRefMatchFailure superPath (Mismatch (patKey, expKey)) = RMMismatch (patKey, expKey)
matchFailureToRefMatchFailure superPath (UnexpectedErrorMatch msg (patKey, expKey)) =
  RMUnexpectedErrorMatch msg (patKey, expKey)

matchThroughReferences :: ExpDeepKey -> Pat -> Exp -> ExceptT ReferenceMatchFailure EvaluateM ReferenceMatchSuccess
matchThroughReferences superPath pat exp = do
  let matchResult = matchPatKeyed pat exp
  let liftedMatchResult = toErrorM $ first (matchFailureToRefMatchFailure superPath) matchResult
  liftedMatchResult `catchNR` \patKey expKey -> do
    failedPat <- fromJustErr "matchThroughReferences: Failing pattern not found?" $ pat L.^? modPatByKeyA patKey
    failedExp <- fromJustErr "matchThroughReferences: Failing expression not found?" $ exp L.^? modExpByKeyA expKey
    undefined
    {-
    Left err@(NeedsReduction (patKey, expKey)) ->
      -- Is failure due to an unexpanded variable?
      let fromJustErr msg = maybe (error msg) id
          failedPat = fromJustErr "matchThroughReferences: Failing pattern not found?" $ pat L.^? modPatByKeyA patKey
          failedExp = fromJustErr "matchThroughReferences: Failing expression not found?" $ exp L.^? modExpByKeyA expKey
      in
      case failedExp of
        VarE name -> do
          lookupResponse <- lookupVariableAbsolute name superPath
          -- Is unexpanded variable a value declaration?
          case lookupResponse of
            LookupVariableFound (ValueDeclaration (Just location) _ (GuardedB body) _) ->
              throwError $ RMVariableHasGuards location
            LookupVariableFound (ValueDeclaration (Just location) letPat (NormalB body) _) ->
              -- Is variable fully reduced (no patterns on left side, no guards?)
              case letPat of
                VarP _ -> do
                  subReferenceMatch <- matchThroughReferences location failedPat body
                  case subReferenceMatch of
                    _ -> undefined -- RMMatchFailure (NeedsReduction (subPatKey, subExpKey)) -> undefined
                    _ -> pure subReferenceMatch
                _ -> throwError $ RMVariableHasPattern location
            _ -> throwError err
        _ -> throwError err
    Left err -> throwError err
    -}
  where
    fromJustErr msg = maybe (throwError $ RMIndexingError msg) pure
    toErrorM = either throwError pure
    catchNR action handler =
      catchError action $ \case
        RMNeedsReduction (patKey, expKey) -> handler patKey expKey
        err -> throwError err
        -}
