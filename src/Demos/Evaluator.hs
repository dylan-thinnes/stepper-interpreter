{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PackageImports #-}
module Demos.Evaluator where

import "base" Data.Functor.Identity

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

import Evaluator
import Lift

x :: Exp
x = $(lift =<< [|
  let t = 10
      k = 1
  in
  case Just t of
    Nothing -> 0
    Just y -> y + 1
  |])

y :: [Exp]
y = iterate (runIdentity . handle emptyEnvironment) x
