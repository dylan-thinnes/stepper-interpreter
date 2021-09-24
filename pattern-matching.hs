{-# LANGUAGE ViewPatterns #-}
module PatternMatching where

import Debug.Trace

eagerPats =
  let f x = Just (x + 3)
      (Just x, Just y) = g "boom"
      g t = (error t, f 7)
  in
  y

lazyPats =
  let f x = Just (x + 3)
      (~(Just x), Just y) = g "boom"
      g t = (error t, f 7)
  in
  y

wildPats =
  let f x = Just (x + 3)
      (_, Just y) = g "boom"
      g t = (error t, f 7)
  in
  y

x@(Just y) = Nothing

patOrder :: Char
patOrder =
  let term =
        ( traceShow "J" $ Just $ traceShow "J1" 1
        , traceShow "L" $ Left $ traceShow "L'x'" 'x'
        )
  in
  case term of
    (traceShow "pat1" -> (Nothing, _)) -> '1' -- should print J
    (traceShow "pat2" -> (_, Right _)) -> '2' -- should print L
    (traceShow "pat3" -> (Nothing, Left _)) -> '3' -- nothing
    (traceShow "pat4" -> (Just _, Right _)) -> '4' -- nothing
    (traceShow "pat5" -> (Just 2, _)) -> '5' -- should print J1
    (traceShow "pat6" -> (_, Left 'y')) -> '6' -- should print L'x'
    (traceShow "patW" -> _) -> '_'
