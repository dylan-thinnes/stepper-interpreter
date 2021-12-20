{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PackageImports #-}
module Lift.Lift where

import "template-haskell" Language.Haskell.TH
import "template-haskell" Language.Haskell.TH.Syntax

instance Lift Bytes where
    lift _ = error "Cannot lift Bytes."
    liftTyped _ = error "Cannot lift Bytes."

deriving instance Lift AnnTarget
deriving instance Lift RuleBndr
deriving instance Lift InjectivityAnn
deriving instance Lift Phases
deriving instance Lift FamilyResultSig
deriving instance Lift RuleMatch
deriving instance Lift Inline
deriving instance Lift FixityDirection
deriving instance Lift Safety
deriving instance Lift Callconv
deriving instance Lift SourceStrictness
deriving instance Lift SourceUnpackedness
deriving instance Lift PkgName
deriving instance Lift NameSpace
deriving instance Lift PatSynDir
deriving instance Lift PatSynArgs
deriving instance Lift DerivStrategy
deriving instance Lift Role
deriving instance Lift TypeFamilyHead
deriving instance Lift TySynEqn
deriving instance Lift Pragma
deriving instance Lift Fixity
deriving instance Lift Foreign
deriving instance Lift Overlap
deriving instance Lift FunDep
deriving instance Lift Bang
deriving instance Lift ModName
deriving instance Lift DerivClause
deriving instance Lift Con
deriving instance Lift Clause
deriving instance Lift Body
deriving instance Lift TyLit
deriving instance Lift TyVarBndr
deriving instance Lift NameFlavour
deriving instance Lift OccName
deriving instance Lift Range
deriving instance Lift Stmt
deriving instance Lift Dec
deriving instance Lift Guard
deriving instance Lift Match
deriving instance Lift Pat
deriving instance Lift Type
deriving instance Lift Lit
deriving instance Lift Name
deriving instance Lift Exp

