{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
module Lift.DeepHoled.Instances where

import Lift.DeepHoled
import Lift.Lift

-- template-haskell
import Language.Haskell.TH.Syntax

-- data-fix
import Data.Fix

-- deriving-compat
import Text.Show.Deriving

-- recursion-schemes
import qualified Data.Functor.Foldable as R

baseFunctorFamily ''Exp

deriveShow1 ''ExpFExp
deriveShow1 ''PatFExp
deriveShow1 ''MatchFExp
deriveShow1 ''SpecialTuple2_0
deriveShow1 ''DecFExp
deriveShow1 ''StmtFExp
deriveShow1 ''RangeFExp
deriveShow1 ''FieldExpFExp
deriveShow1 ''FieldPatFExp
deriveShow1 ''BodyFExp
deriveShow1 ''GuardFExp
deriveShow1 ''ClauseFExp
deriveShow1 ''PragmaFExp
deriveShow1 ''PatSynDirFExp

mkFixG
  :: (Recursive datatype, RecursiveF datatype ~ f, Functor f)
  => datatype -> f (Fix (RecursiveF Exp))
mkFixG datatype = mkFix <$> project datatype

mkFix :: Exp -> Fix (RecursiveF Exp)
mkFix = Fix . mkFixG
