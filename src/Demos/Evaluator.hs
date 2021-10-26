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

x :: Exp
x = $(lift =<< [|
  let t = 10
      k = 1
  in
  case Just t of
    Nothing -> 0
    Just y -> y + 1
  |])

y :: IO ()
y = mapM_ printExp steps
  where
  steps = iterate (runIdentity . handle defaultEnvironment) x
  printExp x = do
    putStrLn "============"
    highlighted <- readProcess "/usr/bin/batcat" (words "-l haskell -pp --color always -") (P.pprint $ P.removeBaseQualifications x)
    putStr highlighted
