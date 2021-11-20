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
      mapMaybe f (x:xs) =
        case f x of
          Nothing -> mapMaybe f xs
          Just y -> y : mapMaybe f xs
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

run :: Exp -> IO ()
run exp = do
  printExp exp
  mapM_ printExp $ map unwrapReductionResult reductionSteps
  where
  run = runIdentity . handle  defaultEnvironment
  steps = iterate (run . unwrapReductionResult) (run exp)
  reductionSteps = takeWhile (not . isCannotReduce) steps
  printExp x = do
    putStrLn "============"
    let source = P.pprint $ P.removeBaseQualifications x
    highlighted <- readProcess "/usr/bin/batcat" (words "--theme zenburn -l haskell -pp --color always -") source
    putStr highlighted
    getLine
