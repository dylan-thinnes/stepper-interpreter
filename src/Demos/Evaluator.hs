{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
module Demos.Evaluator where

import "base" Data.Functor.Identity

import "process" System.Process

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import Evaluator
import Lift
import Ppr qualified as P

testCase :: Exp
testCase = $(lift =<< [|
  let t = 10
      k = 1
  in
  case Just t of
    Nothing -> 0
    Just y -> y + 1
  |])

testCaseOnFuncApp :: Exp
testCaseOnFuncApp = $(lift =<< [|
  let t z = Just (10 + z)
      k = 3
  in
  case t k of
    Nothing -> 0
    Just y -> y * 2
  |])

testListMap :: Exp
testListMap = $(lift =<< [|
  let g x = x * x
      map f (x:xs) = f x : map f xs
      map f [] = []
  in
  map g [1,2,3]
  |])

testSquareOfSum :: Exp
testSquareOfSum = $(lift =<< [|
  let x = 2 + 2
  in
  x * x
  |])

testConstructorsInListMap :: Exp
testConstructorsInListMap = $(lift =<< [|
  let g Nothing = 0
      g (Just x) = x * x
      map f (x:xs) = f x : map f xs
      map f [] = []
  in
  map g [Just 1, Nothing, Just 2, Nothing, Just 3]
  |])

testFilter :: Exp
testFilter = $(lift =<< [|
  let g 0 = False
      g x = True
      filter f (x:xs) = if f x then x : filter f xs else filter f xs
      filter f [] = []
  in
  filter g [1,0,2,0,3,0]
  |])

testMapMaybe :: Exp
testMapMaybe = $(lift =<< [|
  let g 0 = Nothing
      g x = Just (x * x)
      mapMaybe f (x:rest) =
        case f x of
          Nothing -> mapMaybe f rest
          Just y -> y : mapMaybe f rest
      mapMaybe f [] = []
  in
  mapMaybe g [1,0,2,0,3,0]
  |])

testMapAndFilter :: Exp
testMapAndFilter = $(lift =<< [|
  let g 0 = False
      g x = True
      filter f (x:xs) = if f x then x : filter f xs else filter f xs
      filter f [] = []
      h x = x * x
      map f (x:xs) = f x : map f xs
      map f [] = []
  in
  map h (filter g [1,0,2,0,3,0])
  |])

prog :: Exp
prog = $(lift =<< [|
  let f y = Just y
  in
  case f y of
    Nothing -> 0
    Just y -> y
  |])

runDataField :: IO (Either String ReductionResult)
runDataField = run' [d|
  data MyData = X { a :: Int, b :: Int } | Y { c :: Int }
  exp =
    let x = X 1 2
        y = Y 3
    in
    a x + b x + c y
  |]

runMapMaybe :: IO (Either String ReductionResult)
runMapMaybe = run' [d|
  g 0 = Nothing
  g x = Just (x * x)
  mapMaybe f (x:rest) =
    case f x of
      Nothing -> mapMaybe f rest
      Just y -> y : mapMaybe f rest
  mapMaybe f [] = []
  exp = mapMaybe g [1,0,2,0,3,0]
  |]

runCircularPruning :: IO (Either String ReductionResult)
runCircularPruning = run' [d|
  exp =
    let x = 1 + y
        y = 2 + x
        z = 17 -- This should die, because it isn't used
        w = w -- This should die, because it doesn't refer to itself
        t = 7 + t -- This should die, because it refers to itself, but nothing refers to it
    in
    x
  |]

runFoldlSum :: IO (Either String ReductionResult)
runFoldlSum = run' [d|
  foldl' f acc (y:rest) = foldl' f (f acc y) rest
  foldl' f acc [] = acc
  exp =
    foldl' (+) 0 [1,2,3,4]
  |]

run' :: DecsQ -> IO (Either String ReductionResult)
run' decsQ = do
  decs <- runQ decsQ
  let env = envFromDecs decs
  let Just (ValueDeclaration _ (NormalB exp) _) = lookupDefinitionRaw "exp" env
  run env exp

run :: Environment -> Exp -> IO (Either String ReductionResult)
run env exp = do
  putStrLn "Starting environment:"
  putStrLn (debugEnvironment env)
  let oneStep [] = error "Demos.Evaluator.run: empty list - this shouldn't happen"
      oneStep [exp] = do
        printExp exp
        pure exp
      oneStep (exp:rest) = do
        printExp exp
        inp <- getLine
        if null inp then oneStep rest else pure exp
  oneStep reductionSteps
  where
  reductionSteps :: [Either String ReductionResult]
  reductionSteps = takeWhile (either (const True) (not . isCannotReduce)) steps

  steps :: [Either String ReductionResult]
  steps = iterate (\exp -> evaluate env =<< fmap getRedRes exp) (Right $ NewlyReduced Nothing exp)

  printExp :: Either String ReductionResult -> IO ()
  printExp (Left err) =
    putStr $ "Error: " ++ err
  printExp (Right redRes) = do
    putStrLn "============"
    case redRes of
      NewlyReduced (Just reason) _ -> putStrLn $ "Reason: " ++ reason
      _ -> pure ()
    let source = P.pprint $ P.cleanNames (getRedRes redRes)
    highlighted <- readProcess "batcat" (words "--theme zenburn -l haskell -pp --color always -") source
    putStr highlighted
