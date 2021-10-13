{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PackageImports #-}
module Demos.Matching where

import "recursion-schemes" Data.Functor.Foldable qualified as R

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax (Lift(..), Name(..), NameFlavour(..), PkgName(..))

import Ppr qualified as P
import Evaluator

-- Demonstration of matching
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
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.removeBaseQualifications $ P.attachAnn patKey (P.Annotation P.orange Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.removeBaseQualifications $ P.attachAnn expKey (P.Annotation P.orange Nothing) (P.noann exp))
        ]
    Left (NeedsReduction (patKey, expKey)) ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.purple "Following expression needs further reduction to conclusively match."
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.removeBaseQualifications $ P.attachAnn patKey (P.Annotation P.purple Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.removeBaseQualifications $ P.attachAnn expKey (P.Annotation P.purple Nothing) (P.noann exp))
        ]
    Left (UnexpectedErrorMatch msg (patKey, expKey)) ->
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.red "Unexpected error (type system should catch this!): " ++ show msg
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.removeBaseQualifications $ P.attachAnn patKey (P.Annotation P.red Nothing) (P.noann pat))
        , P.boldByANSI "expression: ", P.pprintColoured (P.removeBaseQualifications $ P.attachAnn expKey (P.Annotation P.red Nothing) (P.noann exp))
        ]
    Right bound -> do
      runIO $ putStrLn $ unlines
        [ P.colorByANSI P.green "Following pattern and expression match."
        --, ""
        --, "patkey: " ++ show patKey
        --, "expKey: " ++ show expKey
        --, ""
        , P.boldByANSI "pattern: " ++ P.pprintColoured (P.removeBaseQualifications $ P.noann pat)
        , P.boldByANSI "expression: ", P.pprintColoured (P.removeBaseQualifications $ P.noann exp)
        ]
      runIO $ flip mapM_ (zip [1..] bound) $ \(i, (pat, exp)) -> do
        putStrLn $ P.boldByANSI $ "binding #" ++ show i ++ ": "
        putStr "Pattern: "
        putStrLn $ P.pprintColoured pat
        putStr "Expression: "
        putStrLn $ P.pprintColoured exp
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
    Left (UnexpectedErrorMatch msg keys) -> keys
    Right _ -> error "can't make patKey / expKey because expressions match"
