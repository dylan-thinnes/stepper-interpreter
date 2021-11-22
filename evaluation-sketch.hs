z0 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  case x of
    (Nothing, _) -> 0
    (Just w, ~(Just z)) -> w + z

-- let -> case: Expression needs further reduction to compare against 1st pat
-- Thus, lookup the definition x (found in let binding), replace x with it

z1 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  case f 2 (Just 3) of
    (Nothing, _) -> 0
    (Just w, ~(Just z)) -> w + z

-- let -> case: Expression needs further reduction to compare against 1st pat
-- Thus, apply the function f to all of its arguments

z2 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  case
    let y0 = 2
        m0 = Just 3
     in (Just (y0 * y0), m0)
    of
    (Nothing, _) -> 0
    (Just w, ~(Just z)) -> w + z

-- let -> case: 1st pat has mismatch with expression, try 2nd pat
-- let -> case: 2nd pat matches! bind actuals to reals

z3 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = m0
  in
  w0 + z0

-- let -> let ->
--  +: Left arg is not a literal ->
--    w0 lookup

z4 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = m0
  in
  y0 * y0 + z0

-- let -> let ->
--  +: Left arg is not a literal ->
--    *: Left arg is not a literal ->
--      y0 lookup

z5 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = m0
  in
  2 * y0 + z0

-- let -> let ->
--  +: Left arg is not a literal ->
--    *: Left arg is a literal, Right arg is not a literal ->
--      y0 lookup

z6 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = m0
  in
  2 * 2 + z0

-- let -> let ->
--  +: Left arg is not a literal ->
--    *: Left & right arg are literal, can reduce!

z7 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = m0
  in
  4 + z0

-- let -> let ->
--  +: Left arg is a literal, Right arg is not a literal ->
--    z0 lookup, it's part of a let pattern
--    pattern and expression matching needs reduction
--    reduce the expression for the pattern match to which z0 belongs

z8 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = Just 3
  in
  4 + z0

-- let -> let ->
--  +: Left arg is a literal, Right arg is not a literal ->
--    z0 lookup, it's part of a let pattern
--    pattern and expression now match
--    bind actuals to reals

z8 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = Just 3
  in
  4 + let z0 = 3 in z0

-- let -> let ->
--  +: Left arg is a literal, Right arg is not a literal ->
--    let -> z0
--      z0 lookup

z9 =
  let x = f 2 (Just 3)
      f y m = (Just (y * y), m)
  in
  let w0 = y0 * y0
      Just z0 = Just 3
  in
  4 + let z0 = 3 in 3

-- let -> let ->
--  +: Left arg is a literal, Right arg is not a literal ->
--      z0 lookup

