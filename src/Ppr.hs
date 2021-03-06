{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances #-}
-- | contains a prettyprinter for the
-- Template Haskell datatypes

-- | MODIFIED TO SUPPORT ANNOTATIONS AROUND NODES

module Ppr where
    -- All of the exports from this module should
    -- be "public" functions.  The main module TH
    -- re-exports them all.

import Text.PrettyPrint.Annotated (render, Span(..), renderSpans)
import qualified Text.PrettyPrint.Annotated (annotate)
import Language.Haskell.TH.Syntax
import Data.Word ( Word8 )
import Data.Char ( toLower, chr)
import GHC.Show  ( showMultiLineString )
import GHC.Lexeme( startsVarSym )
import Data.Ratio ( numerator, denominator )
import Prelude hiding ((<>))

import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Fix
import Data.Key (adjust, Key(..), Adjustable(..))
import Data.Bifunctor (bimap)
import Data.Generics.Uniplate.Data
import qualified Data.Data as DD

import qualified Data.Functor.Foldable as R
import Lift
import Lift.DeepRecursive as DR
import Lift.DeepRecursive.Instances as DR

import Ppr.Lib hiding (Doc)
import qualified Ppr.Lib

-- annotations
type Annotated f = Fix (Ann (Maybe Annotation) f)
type AnnotatedExp = Annotated ExpF
type AnnotatedPat = Annotated PatF

noann :: (Functor f, R.Corecursive t, R.Recursive t, f ~ R.Base t) => t -> Annotated f
noann = R.hoist (Pair (Const Nothing))

attachAnn :: (Adjustable f, Functor f, Traversable f) => [Key f] -> Annotation -> Annotated f -> Annotated f
attachAnn key ann = adjustRecursiveG modify key setAnn
  where
    setAnn (Fix (Pair _ expf)) = Fix $ Pair (Const (Just ann)) expf
    modify f key (Pair ann expf) = Pair ann $ adjust f key expf

attachAnnExp :: ExpKey -> Annotation -> AnnotatedExp -> AnnotatedExp
attachAnnExp = attachAnn

attachAnnPat :: PatKey -> Annotation -> AnnotatedPat -> AnnotatedPat
attachAnnPat = attachAnn

type Color = (Word8, Word8, Word8)

colorByANSI :: Color -> String -> String
colorByANSI (r,g,b) str = concat ["\ESC[48;2;", show r, ";", show g, ";", show b, "m", str, "\ESC[0m"]

boldByANSI :: String -> String
boldByANSI str = "\ESC[1m" ++ str ++ "\ESC[0m"

red, blue, green, purple, orange :: Color
red = (255,0,0)
blue = (0,0,255)
green = (0,127,0)
purple = (100,0,200)
orange = (200,100,0)

data Annotation = Annotation { color :: Color, info :: Maybe String }
  deriving (Show, DD.Data)

pprintColoured :: Ppr a => a -> String
pprintColoured annexp = foldr colourSpan source spans
  where
    (source, spans) = pprintSpans annexp
    colourSpan :: Span Annotation -> String -> String
    colourSpan (Span { spanStart, spanLength, spanAnnotation = Annotation { color, info } }) str =
      let (pre, rest) = splitAt spanStart str
          (text, post) = splitAt spanLength rest
      in
      pre ++ colorByANSI color text ++ post

-- removing qualified names from base package for simpler pprinting
cleanNames :: (DD.Data from, Biplate from Name) => from -> from
cleanNames = transformAllNames (toStandalone . removeBaseQualifications)
  where
    -- remove mentions of common packages
    removeBaseQualifications name
      | (Name occName (NameG namespace pkgName modName)) <- name
      , or
          [ pkgName == PkgName "base"
          , pkgName == PkgName "ghc-prim"
          ]
      = Name occName NameS
      | otherwise
      = name

    -- change local NameU to NameS, so as to remove many underscores
    -- later, may want to preserve underscores as necessary by checking for unique names
    toStandalone (Name occName (NameU _)) = Name occName NameS
    toStandalone name = name

-- document
type Doc = Ppr.Lib.Doc Annotation

nestDepth :: Int
nestDepth = 4

type Precedence = Int
appPrec, opPrec, unopPrec, sigPrec, noPrec :: Precedence
appPrec  = 4    -- Argument of a function application
opPrec   = 3    -- Argument of an infix operator
unopPrec = 2    -- Argument of an unresolved infix operator
sigPrec  = 1    -- Argument of an explicit type signature
noPrec   = 0    -- Others

parensIf :: Bool -> Doc -> Doc
parensIf True d = parens d
parensIf False d = d

------------------------------

pprint :: Ppr a => a -> String
pprint x = render $ to_HPJ_Doc $ ppr x

pprintSpans :: Ppr a => a -> (String, [Span Annotation])
pprintSpans x = renderSpans $ to_HPJ_Doc $ ppr x

class Ppr a where
    ppr :: a -> Doc
    ppr_list :: [a] -> Doc
    ppr_list = vcat . map ppr

instance Ppr a => Ppr [a] where
    ppr x = ppr_list x

------------------------------
instance Ppr Name where
    ppr v = pprName v

------------------------------
instance Ppr Info where
    ppr (TyConI d)     = ppr d
    ppr (ClassI d is)  = ppr d $$ vcat (map ppr is)
    ppr (FamilyI d is) = ppr d $$ vcat (map ppr is)
    ppr (PrimTyConI name arity is_unlifted)
      = text "Primitive"
        <+> (if is_unlifted then text "unlifted" else empty)
        <+> text "type constructor" <+> quotes (ppr name)
        <+> parens (text "arity" <+> int arity)
    ppr (ClassOpI v ty cls)
      = text "Class op from" <+> ppr cls <> colon <+> ppr_sig v ty
    ppr (DataConI v ty tc)
      = text "Constructor from" <+> ppr tc <> colon <+> ppr_sig v ty
    ppr (PatSynI nm ty) = pprPatSynSig nm ty
    ppr (TyVarI v ty)
      = text "Type variable" <+> ppr v <+> equals <+> ppr ty
    ppr (VarI v ty mb_d)
      = vcat [ppr_sig v ty,
              case mb_d of { Nothing -> empty; Just d -> ppr d }]

ppr_sig :: Name -> Type -> Doc
ppr_sig v ty = pprName' Applied v <+> dcolon <+> ppr ty

pprFixity :: Name -> Fixity -> Doc
pprFixity _ f | f == defaultFixity = empty
pprFixity v (Fixity i d) = ppr_fix d <+> int i <+> ppr v
    where ppr_fix InfixR = text "infixr"
          ppr_fix InfixL = text "infixl"
          ppr_fix InfixN = text "infix"

-- | Pretty prints a pattern synonym type signature
pprPatSynSig :: Name -> PatSynType -> Doc
pprPatSynSig nm ty
  = text "pattern" <+> pprPrefixOcc nm <+> dcolon <+> pprPatSynType ty

-- | Pretty prints a pattern synonym's type; follows the usual
-- conventions to print a pattern synonym type compactly, yet
-- unambiguously. See the note on 'PatSynType' and the section on
-- pattern synonyms in the GHC user's guide for more information.
pprPatSynType :: PatSynType -> Doc
pprPatSynType ty@(ForallT uniTys reqs ty'@(ForallT exTys provs ty''))
  | null exTys,  null provs = ppr (ForallT uniTys reqs ty'')
  | null uniTys, null reqs  = noreqs <+> ppr ty'
  | null reqs               = forall uniTys <+> noreqs <+> ppr ty'
  | otherwise               = ppr ty
  where noreqs     = text "() =>"
        forall tvs = text "forall" <+> (hsep (map ppr tvs)) <+> text "."
pprPatSynType ty            = ppr ty

------------------------------
instance Ppr Module where
  ppr (Module pkg m) = text (pkgString pkg) <+> text (modString m)

instance Ppr ModuleInfo where
  ppr (ModuleInfo imps) = text "Module" <+> vcat (map ppr imps)

------------------------------
instance Ppr Exp where
    ppr = pprExp noPrec . noann

instance Ppr AnnotatedExp where
    ppr = pprExp noPrec

pprPrefixOcc :: Name -> Doc
-- Print operators with parens around them
pprPrefixOcc n = parensIf (isSymOcc n) (ppr n)

isSymOcc :: Name -> Bool
isSymOcc n
  = case nameBase n of
      []    -> True  -- Empty name; weird
      (c:_) -> startsVarSym c
                   -- c.f. OccName.startsVarSym in GHC itself

instance Ppr (a, Precedence -> Doc) where
  ppr (_, cont) = cont noPrec

pprInfixExp :: AnnotatedExp -> Doc
pprInfixExp exp@(Fix (Pair (Const mann) expf)) =
  case expf of
    VarEFExp v -> pprName' Infix v
    ConEFExp v -> pprName' Infix v
    UnboundVarEFExp v -> pprName' Infix v
    -- This case will only ever be reached in exceptional circumstances.
    -- For example, when printing an error message in case of a malformed expression.
    _ -> text "`" <> pprExp noPrec exp <> text "`"

pprExp :: Precedence -> AnnotatedExp -> Doc
pprExp prec exp = R.para alg exp prec
  where
    alg (Pair (Const mann) expf) prec = mannotate mann $ pprExpF prec expf

pprExp' :: Precedence -> (AnnotatedExp, Precedence -> Doc) -> Doc
pprExp' prec (_, cont) = cont prec

deannDeepRec :: forall t f a. (DR.DeepRecursive t, f ~ DR.DeepRecursiveF t, Functor f) => f (AnnotatedExp, a) -> t
deannDeepRec = DR.embed . fmap (first (R.hoist (\(Pair _ fa) -> fa)))
  where
    first f (a, b) = f a

pprExpF :: Precedence -> ExpF (AnnotatedExp, Precedence -> Doc) -> Doc
pprExpF _ (VarEFExp v)     = pprName' Applied v
pprExpF _ (ConEFExp c)     = pprName' Applied c
pprExpF i (LitEFExp l)     = pprLit i l
pprExpF i (AppEFExp e1 e2) = parensIf (i >= appPrec) $ pprExp' opPrec e1
                                              <+> pprExp' appPrec e2
pprExpF i (AppTypeEFExp e t)
 = parensIf (i >= appPrec) $ pprExp' opPrec e <+> char '@' <> pprParendType t
pprExpF _ (ParensEFExp e)  = parens (pprExp' noPrec e)
pprExpF i (UInfixEFExp e1 op e2)
 = parensIf (i > unopPrec) $ pprExp' unopPrec e1
                         <+> pprInfixExp (fst op)
                         <+> pprExp' unopPrec e2
pprExpF i (InfixEFExp (Just e1) op (Just e2))
 = parensIf (i >= opPrec) $ pprExp' opPrec e1
                        <+> pprInfixExp (fst op)
                        <+> pprExp' opPrec e2
pprExpF _ (InfixEFExp me1 op me2) = parens $ pprMaybeExp noPrec me1
                                    <+> pprInfixExp (fst op)
                                    <+> pprMaybeExp noPrec me2
pprExpF i (LamEFExp [] e) = pprExp' i e -- #13856
pprExpF i (LamEFExp ps e) = parensIf (i > noPrec) $ char '\\' <> hsep (map (pprPatNoAnn appPrec . deannDeepRec) ps)
                                           <+> text "->" <+> ppr e
pprExpF i (LamCaseEFExp ms) = parensIf (i > noPrec)
                       $ text "\\case" $$ nest nestDepth (ppr $ map (deannDeepRec @Match) ms)
pprExpF i (TupEFExp es)
  | [Just e] <- es
  = pprExp i (Fix $ Pair (Const Nothing) $ AppEFExp (Fix $ Pair (Const Nothing) (ConEFExp (tupleDataName 1))) (fst e))
  | otherwise
  = parens (commaSepWith (pprMaybeExp noPrec) es)
pprExpF _ (UnboxedTupEFExp es) = hashParens (commaSepWith (pprMaybeExp noPrec) es)
pprExpF _ (UnboxedSumEFExp e alt arity) = unboxedSumBars (ppr e) alt arity
-- Nesting in Cond is to avoid potential problems in do statements
pprExpF i (CondEFExp guard true false)
 = parensIf (i > noPrec) $ sep [text "if"   <+> ppr guard,
                       nest 1 $ text "then" <+> ppr true,
                       nest 1 $ text "else" <+> ppr false]
pprExpF i (MultiIfEFExp alts)
  = parensIf (i > noPrec) $ vcat $
      case alts of
        []            -> [text "if {}"]
        (alt : alts') -> text "if" <+> pprGuarded arrow (deannST alt)
                         : map (nest 3 . pprGuarded arrow) (deannST <$> alts')
  where
    deannST (ST2_0 guardedFExp exp) = (deannDeepRec guardedFExp, deann $ fst exp)
pprExpF i (LetEFExp ds_ e) = parensIf (i > noPrec) $ text "let" <+> pprDecs (map (deannDeepRec @Dec) ds_)
                                             $$ text " in" <+> ppr e
  where
    pprDecs []  = empty
    pprDecs [d] = ppr d
    pprDecs ds  = braces (semiSep ds)

pprExpF i (CaseEFExp e ms)
 = parensIf (i > noPrec) $ text "case" <+> ppr e <+> text "of"
                        $$ nest nestDepth (ppr $ map (deannDeepRec @Match) ms)
pprExpF i (DoEFExp ss_) = parensIf (i > noPrec) $ text "do" <+> pprStms (map (deannDeepRec @Stmt) ss_)
  where
    pprStms []  = empty
    pprStms [s] = ppr s
    pprStms ss  = braces (semiSep ss)
pprExpF i (MDoEFExp ss_) = parensIf (i > noPrec) $ text "mdo" <+> pprStms (map (deannDeepRec @Stmt) ss_)
  where
    pprStms []  = empty
    pprStms [s] = ppr s
    pprStms ss  = braces (semiSep ss)

pprExpF _ (CompEFExp []) = text "<<Empty CompExp>>"
-- This will probably break with fixity declarations - would need a ';'
pprExpF _ (CompEFExp ss) =
    if null ss'
       -- If there are no statements in a list comprehension besides the last
       -- one, we simply treat it like a normal list.
       then text "[" <> ppr (deannDeepRec @Stmt s) <> text "]"
       else text "[" <> ppr (deannDeepRec @Stmt s)
        <+> bar
        <+> commaSep (map (deannDeepRec @Stmt) ss')
         <> text "]"
  where s = last ss
        ss' = init ss
pprExpF _ (ArithSeqEFExp d) = ppr (deannDeepRec @Range d)
pprExpF _ (ListEFExp es) = brackets (commaSep es)
pprExpF i (SigEFExp e t) = parensIf (i > noPrec) $ pprExp' sigPrec e
                                          <+> dcolon <+> ppr t
pprExpF _ (RecConEFExp nm fs) = ppr nm <> braces (pprFields $ map fieldExpToTuple fs)
  where
    fieldExpToTuple (FieldExpFExp name exp) = (name, exp)
pprExpF _ (RecUpdEFExp e fs) = pprExp' appPrec e <> braces (pprFields $ map fieldExpToTuple fs)
  where
    fieldExpToTuple (FieldExpFExp name exp) = (name, exp)
pprExpF i (StaticEFExp e) = parensIf (i >= appPrec) $
                         text "static"<+> pprExp' appPrec e
pprExpF _ (UnboundVarEFExp v) = pprName' Applied v
pprExpF _ (LabelEFExp s) = text "#" <> text s
pprExpF _ (ImplicitParamVarEFExp n) = text ('?' : n)

pprFields :: [(Name,(AnnotatedExp, Precedence -> Doc))] -> Doc
pprFields = sep . punctuate comma . map (\(s,e) -> ppr s <+> equals <+> ppr e)

pprMaybeExp :: Precedence -> Maybe (AnnotatedExp, Precedence -> Doc) -> Doc
pprMaybeExp _ Nothing = empty
pprMaybeExp i (Just e) = pprExp' i e

------------------------------
instance Ppr Stmt where
    ppr (BindS p e) = ppr p <+> text "<-" <+> ppr e
    ppr (LetS ds) = text "let" <+> (braces (semiSep ds))
    ppr (NoBindS e) = ppr e
    ppr (ParS sss) = sep $ punctuate bar
                         $ map commaSep sss
    ppr (RecS ss) = text "rec" <+> (braces (semiSep ss))

------------------------------
instance Ppr Match where
    ppr (Match p rhs ds) = pprMatchPat p <+> pprBody False rhs
                        $$ where_clause ds

pprMatchPat :: Pat -> Doc
-- Everything except pattern signatures bind more tightly than (->)
pprMatchPat p@(SigP {}) = parens (ppr p)
pprMatchPat p           = ppr p

------------------------------
pprGuarded :: Doc -> (Guard, Exp) -> Doc
pprGuarded eqDoc (guard, expr) = case guard of
  NormalG guardExpr -> bar <+> ppr guardExpr <+> eqDoc <+> ppr expr
  PatG    stmts     -> bar <+> vcat (punctuate comma $ map ppr stmts) $$
                         nest nestDepth (eqDoc <+> ppr expr)

------------------------------
pprBody :: Bool -> Body -> Doc
pprBody eq body = case body of
    GuardedB xs -> nest nestDepth $ vcat $ map (pprGuarded eqDoc) xs
    NormalB  e  -> eqDoc <+> ppr e
  where eqDoc | eq        = equals
              | otherwise = arrow

------------------------------
instance Ppr Lit where
  ppr = pprLit noPrec

pprLit :: Precedence -> Lit -> Doc
pprLit i (IntPrimL x)    = parensIf (i > noPrec && x < 0)
                                    (integer x <> char '#')
pprLit _ (WordPrimL x)    = integer x <> text "##"
pprLit i (FloatPrimL x)  = parensIf (i > noPrec && x < 0)
                                    (float (fromRational x) <> char '#')
pprLit i (DoublePrimL x) = parensIf (i > noPrec && x < 0)
                                    (double (fromRational x) <> text "##")
pprLit i (IntegerL x)    = parensIf (i > noPrec && x < 0) (integer x)
pprLit _ (CharL c)       = text (show c)
pprLit _ (CharPrimL c)   = text (show c) <> char '#'
pprLit _ (StringL s)     = pprString s
pprLit _ (StringPrimL s) = pprString (bytesToString s) <> char '#'
pprLit _ (BytesPrimL {}) = pprString "<binary data>"
pprLit i (RationalL rat) = parensIf (i > noPrec) $
                           integer (numerator rat) <+> char '/'
                              <+> integer (denominator rat)

bytesToString :: [Word8] -> String
bytesToString = map (chr . fromIntegral)

pprString :: String -> Doc
-- Print newlines as newlines with Haskell string escape notation,
-- not as '\n'.  For other non-printables use regular escape notation.
pprString s = vcat (map text (showMultiLineString s))

------------------------------
instance Ppr Pat where
    ppr = pprPatNoAnn noPrec

instance Ppr AnnotatedPat where
    ppr = pprPat noPrec

pprPat :: Precedence -> AnnotatedPat -> Doc
pprPat prec pat = R.para alg pat prec
  where
    alg (Pair (Const mann) patf) prec = mannotate mann $ pprPatF prec patf

pprPatNoAnn :: Precedence -> Pat -> Doc
pprPatNoAnn prec pat = pprPat prec (noann pat)

pprPat' :: Precedence -> (AnnotatedPat, Precedence -> Doc) -> Doc
pprPat' prec (_, cont) = cont prec

pprPatF :: Precedence -> PatF (AnnotatedPat, Precedence -> Doc) -> Doc
pprPatF i (LitPF l)     = pprLit i l
pprPatF _ (VarPF v)     = pprName' Applied v
pprPatF i (TupPF ps)
  | [_] <- ps
  = pprPat i (Fix $ Pair (Const Nothing) $ ConPF (tupleDataName 1) (fst <$> ps))
  | otherwise
  = parens (commaSep ps)
pprPatF _ (UnboxedTupPF ps) = hashParens (commaSep ps)
pprPatF _ (UnboxedSumPF p alt arity) = unboxedSumBars (ppr p) alt arity
pprPatF i (ConPF s ps)  = parensIf (i >= appPrec) $ pprName' Applied s
                                              <+> sep (map (pprPat' appPrec) ps)
pprPatF _ (ParensPF p)  = parens $ pprPat' noPrec p
pprPatF i (UInfixPF p1 n p2)
                      = parensIf (i > unopPrec) (pprPat' unopPrec p1 <+>
                                                 pprName' Infix n   <+>
                                                 pprPat' unopPrec p2)
pprPatF i (InfixPF p1 n p2)
                      = parensIf (i >= opPrec) (pprPat' opPrec p1 <+>
                                                pprName' Infix n <+>
                                                pprPat' opPrec p2)
pprPatF i (TildePF p)   = parensIf (i > noPrec) $ char '~' <> pprPat' appPrec p
pprPatF i (BangPF p)    = parensIf (i > noPrec) $ char '!' <> pprPat' appPrec p
pprPatF i (AsPF v p)    = parensIf (i > noPrec) $ ppr v <> text "@"
                                                      <> pprPat' appPrec p
pprPatF _ WildPF        = text "_"
pprPatF _ (RecPF nm fs)
 = parens $     ppr nm
            <+> braces (sep $ punctuate comma $
                        map (\(s,p) -> ppr s <+> equals <+> ppr p) fs)
pprPatF _ (ListPF ps) = brackets (commaSep ps)
pprPatF i (SigPF p t) = parensIf (i > noPrec) $ ppr p <+> dcolon <+> ppr t
pprPatF _ (ViewPF e p) = parens $ pprExp noPrec (noann e) <+> text "->" <+> pprPat' noPrec p

------------------------------
instance Ppr Dec where
    ppr = ppr_dec True

ppr_dec :: Bool     -- declaration on the toplevel?
        -> Dec
        -> Doc
ppr_dec _ (FunD f cs)   = vcat $ map (\c -> pprPrefixOcc f <+> ppr c) cs
ppr_dec _ (ValD p r ds) = ppr p <+> pprBody True r
                          $$ where_clause ds
ppr_dec _ (TySynD t xs rhs)
  = ppr_tySyn empty (Just t) (hsep (map ppr xs)) rhs
ppr_dec _ (DataD ctxt t xs ksig cs decs)
  = ppr_data empty ctxt (Just t) (hsep (map ppr xs)) ksig cs decs
ppr_dec _ (NewtypeD ctxt t xs ksig c decs)
  = ppr_newtype empty ctxt (Just t) (sep (map ppr xs)) ksig c decs
ppr_dec _  (ClassD ctxt c xs fds ds)
  = text "class" <+> pprCxt ctxt <+> ppr c <+> hsep (map ppr xs) <+> ppr fds
    $$ where_clause ds
ppr_dec _ (InstanceD o ctxt i ds) =
        text "instance" <+> maybe empty ppr_overlap o <+> pprCxt ctxt <+> ppr i
                                  $$ where_clause ds
ppr_dec _ (SigD f t)    = pprPrefixOcc f <+> dcolon <+> ppr t
ppr_dec _ (KiSigD f k)  = text "type" <+> pprPrefixOcc f <+> dcolon <+> ppr k
ppr_dec _ (ForeignD f)  = ppr f
ppr_dec _ (InfixD fx n) = pprFixity n fx
ppr_dec _ (PragmaD p)   = ppr p
ppr_dec isTop (DataFamilyD tc tvs kind)
  = text "data" <+> maybeFamily <+> ppr tc <+> hsep (map ppr tvs) <+> maybeKind
  where
    maybeFamily | isTop     = text "family"
                | otherwise = empty
    maybeKind | (Just k') <- kind = dcolon <+> ppr k'
              | otherwise = empty
ppr_dec isTop (DataInstD ctxt bndrs ty ksig cs decs)
  = ppr_data (maybeInst <+> ppr_bndrs bndrs)
             ctxt Nothing (ppr ty) ksig cs decs
  where
    maybeInst | isTop     = text "instance"
              | otherwise = empty
ppr_dec isTop (NewtypeInstD ctxt bndrs ty ksig c decs)
  = ppr_newtype (maybeInst <+> ppr_bndrs bndrs)
                ctxt Nothing (ppr ty) ksig c decs
  where
    maybeInst | isTop     = text "instance"
              | otherwise = empty
ppr_dec isTop (TySynInstD (TySynEqn mb_bndrs ty rhs))
  = ppr_tySyn (maybeInst <+> ppr_bndrs mb_bndrs)
              Nothing (ppr ty) rhs
  where
    maybeInst | isTop     = text "instance"
              | otherwise = empty
ppr_dec isTop (OpenTypeFamilyD tfhead)
  = text "type" <+> maybeFamily <+> ppr_tf_head tfhead
  where
    maybeFamily | isTop     = text "family"
                | otherwise = empty
ppr_dec _ (ClosedTypeFamilyD tfhead eqns)
  = hang (text "type family" <+> ppr_tf_head tfhead <+> text "where")
      nestDepth (vcat (map ppr_eqn eqns))
  where
    ppr_eqn (TySynEqn mb_bndrs lhs rhs)
      = ppr_bndrs mb_bndrs <+> ppr lhs <+> text "=" <+> ppr rhs
ppr_dec _ (RoleAnnotD name roles)
  = hsep [ text "type role", ppr name ] <+> hsep (map ppr roles)
ppr_dec _ (StandaloneDerivD ds cxt ty)
  = hsep [ text "deriving"
         , maybe empty ppr_deriv_strategy ds
         , text "instance"
         , pprCxt cxt
         , ppr ty ]
ppr_dec _ (DefaultSigD n ty)
  = hsep [ text "default", pprPrefixOcc n, dcolon, ppr ty ]
ppr_dec _ (PatSynD name args dir pat)
  = text "pattern" <+> pprNameArgs <+> ppr dir <+> pprPatRHS
  where
    pprNameArgs | InfixPatSyn a1 a2 <- args = ppr a1 <+> ppr name <+> ppr a2
                | otherwise                 = ppr name <+> ppr args
    pprPatRHS   | ExplBidir cls <- dir = hang (ppr pat <+> text "where")
                                           nestDepth (ppr name <+> ppr cls)
                | otherwise            = ppr pat
ppr_dec _ (PatSynSigD name ty)
  = pprPatSynSig name ty
ppr_dec _ (ImplicitParamBindD n e)
  = hsep [text ('?' : n), text "=", ppr e]

ppr_deriv_strategy :: DerivStrategy -> Doc
ppr_deriv_strategy ds =
  case ds of
    StockStrategy    -> text "stock"
    AnyclassStrategy -> text "anyclass"
    NewtypeStrategy  -> text "newtype"
    ViaStrategy ty   -> text "via" <+> pprParendType ty

ppr_overlap :: Overlap -> Doc
ppr_overlap o = text $
  case o of
    Overlaps      -> "{-# OVERLAPS #-}"
    Overlappable  -> "{-# OVERLAPPABLE #-}"
    Overlapping   -> "{-# OVERLAPPING #-}"
    Incoherent    -> "{-# INCOHERENT #-}"

ppr_data :: Doc -> Cxt -> Maybe Name -> Doc -> Maybe Kind -> [Con] -> [DerivClause]
         -> Doc
ppr_data maybeInst ctxt t argsDoc ksig cs decs
  = sep [text "data" <+> maybeInst
            <+> pprCxt ctxt
            <+> case t of
                 Just n -> pprName' Applied n <+> argsDoc
                 Nothing -> argsDoc
            <+> ksigDoc <+> maybeWhere,
         nest nestDepth (sep (pref $ map ppr cs)),
         if null decs
           then empty
           else nest nestDepth
              $ vcat $ map ppr_deriv_clause decs]
  where
    pref :: [Doc] -> [Doc]
    pref xs | isGadtDecl = xs
    pref []              = []      -- No constructors; can't happen in H98
    pref (d:ds)          = (char '=' <+> d):map (bar <+>) ds

    maybeWhere :: Doc
    maybeWhere | isGadtDecl = text "where"
               | otherwise  = empty

    isGadtDecl :: Bool
    isGadtDecl = not (null cs) && all isGadtCon cs
        where isGadtCon (GadtC _ _ _   ) = True
              isGadtCon (RecGadtC _ _ _) = True
              isGadtCon (ForallC _ _ x ) = isGadtCon x
              isGadtCon  _               = False

    ksigDoc = case ksig of
                Nothing -> empty
                Just k  -> dcolon <+> ppr k

ppr_newtype :: Doc -> Cxt -> Maybe Name -> Doc -> Maybe Kind -> Con -> [DerivClause]
            -> Doc
ppr_newtype maybeInst ctxt t argsDoc ksig c decs
  = sep [text "newtype" <+> maybeInst
            <+> pprCxt ctxt
            <+> case t of
                 Just n -> ppr n <+> argsDoc
                 Nothing -> argsDoc
            <+> ksigDoc,
         nest 2 (char '=' <+> ppr c),
         if null decs
           then empty
           else nest nestDepth
                $ vcat $ map ppr_deriv_clause decs]
  where
    ksigDoc = case ksig of
                Nothing -> empty
                Just k  -> dcolon <+> ppr k

ppr_deriv_clause :: DerivClause -> Doc
ppr_deriv_clause (DerivClause ds ctxt)
  = text "deriving" <+> pp_strat_before
                    <+> ppr_cxt_preds ctxt
                    <+> pp_strat_after
  where
    -- @via@ is unique in that in comes /after/ the class being derived,
    -- so we must special-case it.
    (pp_strat_before, pp_strat_after) =
      case ds of
        Just (via@ViaStrategy{}) -> (empty, ppr_deriv_strategy via)
        _                        -> (maybe empty ppr_deriv_strategy ds, empty)

ppr_tySyn :: Doc -> Maybe Name -> Doc -> Type -> Doc
ppr_tySyn maybeInst t argsDoc rhs
  = text "type" <+> maybeInst
    <+> case t of
         Just n -> ppr n <+> argsDoc
         Nothing -> argsDoc
    <+> text "=" <+> ppr rhs

ppr_tf_head :: TypeFamilyHead -> Doc
ppr_tf_head (TypeFamilyHead tc tvs res inj)
  = ppr tc <+> hsep (map ppr tvs) <+> ppr res <+> maybeInj
  where
    maybeInj | (Just inj') <- inj = ppr inj'
             | otherwise          = empty

ppr_bndrs :: Maybe [TyVarBndr] -> Doc
ppr_bndrs (Just bndrs) = text "forall" <+> sep (map ppr bndrs) <> text "."
ppr_bndrs Nothing = empty

------------------------------
instance Ppr FunDep where
    ppr (FunDep xs ys) = hsep (map ppr xs) <+> text "->" <+> hsep (map ppr ys)
    ppr_list [] = empty
    ppr_list xs = bar <+> commaSep xs

------------------------------
instance Ppr FamilyResultSig where
    ppr NoSig           = empty
    ppr (KindSig k)     = dcolon <+> ppr k
    ppr (TyVarSig bndr) = text "=" <+> ppr bndr

------------------------------
instance Ppr InjectivityAnn where
    ppr (InjectivityAnn lhs rhs) =
        bar <+> ppr lhs <+> text "->" <+> hsep (map ppr rhs)

------------------------------
instance Ppr Foreign where
    ppr (ImportF callconv safety impent as typ)
       = text "foreign import"
     <+> showtextl callconv
     <+> showtextl safety
     <+> text (show impent)
     <+> ppr as
     <+> dcolon <+> ppr typ
    ppr (ExportF callconv expent as typ)
        = text "foreign export"
      <+> showtextl callconv
      <+> text (show expent)
      <+> ppr as
      <+> dcolon <+> ppr typ

------------------------------
instance Ppr Pragma where
    ppr (InlineP n inline rm phases)
       = text "{-#"
     <+> ppr inline
     <+> ppr rm
     <+> ppr phases
     <+> ppr n
     <+> text "#-}"
    ppr (SpecialiseP n ty inline phases)
       =   text "{-# SPECIALISE"
       <+> maybe empty ppr inline
       <+> ppr phases
       <+> sep [ ppr n <+> dcolon
               , nest 2 $ ppr ty ]
       <+> text "#-}"
    ppr (SpecialiseInstP inst)
       = text "{-# SPECIALISE instance" <+> ppr inst <+> text "#-}"
    ppr (RuleP n ty_bndrs tm_bndrs lhs rhs phases)
       = sep [ text "{-# RULES" <+> pprString n <+> ppr phases
             , nest 4 $ ppr_ty_forall ty_bndrs <+> ppr_tm_forall ty_bndrs
                                               <+> ppr lhs
             , nest 4 $ char '=' <+> ppr rhs <+> text "#-}" ]
      where ppr_ty_forall Nothing      = empty
            ppr_ty_forall (Just bndrs) = text "forall"
                                         <+> fsep (map ppr bndrs)
                                         <+> char '.'
            ppr_tm_forall Nothing | null tm_bndrs = empty
            ppr_tm_forall _ = text "forall"
                              <+> fsep (map ppr tm_bndrs)
                              <+> char '.'
    ppr (AnnP tgt expr)
       = text "{-# ANN" <+> target1 tgt <+> ppr expr <+> text "#-}"
      where target1 ModuleAnnotation    = text "module"
            target1 (TypeAnnotation t)  = text "type" <+> ppr t
            target1 (ValueAnnotation v) = ppr v
    ppr (LineP line file)
       = text "{-# LINE" <+> int line <+> text (show file) <+> text "#-}"
    ppr (CompleteP cls mty)
       = text "{-# COMPLETE" <+> (fsep $ punctuate comma $ map ppr cls)
                <+> maybe empty (\ty -> dcolon <+> ppr ty) mty

------------------------------
instance Ppr Inline where
    ppr NoInline  = text "NOINLINE"
    ppr Inline    = text "INLINE"
    ppr Inlinable = text "INLINABLE"

------------------------------
instance Ppr RuleMatch where
    ppr ConLike = text "CONLIKE"
    ppr FunLike = empty

------------------------------
instance Ppr Phases where
    ppr AllPhases       = empty
    ppr (FromPhase i)   = brackets $ int i
    ppr (BeforePhase i) = brackets $ char '~' <> int i

------------------------------
instance Ppr RuleBndr where
    ppr (RuleVar n)         = ppr n
    ppr (TypedRuleVar n ty) = parens $ ppr n <+> dcolon <+> ppr ty

------------------------------
instance Ppr Clause where
    ppr (Clause ps rhs ds) = hsep (map (pprPatNoAnn appPrec) ps) <+> pprBody True rhs
                             $$ where_clause ds

------------------------------
instance Ppr Con where
    ppr (NormalC c sts) = ppr c <+> sep (map pprBangType sts)

    ppr (RecC c vsts)
        = ppr c <+> braces (sep (punctuate comma $ map pprVarBangType vsts))

    ppr (InfixC st1 c st2) = pprBangType st1
                         <+> pprName' Infix c
                         <+> pprBangType st2

    ppr (ForallC ns ctxt (GadtC c sts ty))
        = commaSepApplied c <+> dcolon <+> pprForall ns ctxt
      <+> pprGadtRHS sts ty

    ppr (ForallC ns ctxt (RecGadtC c vsts ty))
        = commaSepApplied c <+> dcolon <+> pprForall ns ctxt
      <+> pprRecFields vsts ty

    ppr (ForallC ns ctxt con)
        = pprForall ns ctxt <+> ppr con

    ppr (GadtC c sts ty)
        = commaSepApplied c <+> dcolon <+> pprGadtRHS sts ty

    ppr (RecGadtC c vsts ty)
        = commaSepApplied c <+> dcolon <+> pprRecFields vsts ty

instance Ppr PatSynDir where
  ppr Unidir        = text "<-"
  ppr ImplBidir     = text "="
  ppr (ExplBidir _) = text "<-"
    -- the ExplBidir's clauses are pretty printed together with the
    -- entire pattern synonym; so only print the direction here.

instance Ppr PatSynArgs where
  ppr (PrefixPatSyn args) = sep $ map ppr args
  ppr (InfixPatSyn a1 a2) = ppr a1 <+> ppr a2
  ppr (RecordPatSyn sels) = braces $ sep (punctuate comma (map ppr sels))

commaSepApplied :: [Name] -> Doc
commaSepApplied = commaSepWith (pprName' Applied)

pprForall :: [TyVarBndr] -> Cxt -> Doc
pprForall = pprForall' ForallInvis

pprForallVis :: [TyVarBndr] -> Cxt -> Doc
pprForallVis = pprForall' ForallVis

pprForall' :: ForallVisFlag -> [TyVarBndr] -> Cxt -> Doc
pprForall' fvf tvs cxt
  -- even in the case without any tvs, there could be a non-empty
  -- context cxt (e.g., in the case of pattern synonyms, where there
  -- are multiple forall binders and contexts).
  | [] <- tvs = pprCxt cxt
  | otherwise = text "forall" <+> hsep (map ppr tvs)
                              <+> separator <+> pprCxt cxt
  where
    separator = case fvf of
                  ForallVis   -> text "->"
                  ForallInvis -> char '.'

pprRecFields :: [(Name, Strict, Type)] -> Type -> Doc
pprRecFields vsts ty
    = braces (sep (punctuate comma $ map pprVarBangType vsts))
  <+> arrow <+> ppr ty

pprGadtRHS :: [(Strict, Type)] -> Type -> Doc
pprGadtRHS [] ty
    = ppr ty
pprGadtRHS sts ty
    = sep (punctuate (space <> arrow) (map pprBangType sts))
  <+> arrow <+> ppr ty

------------------------------
pprVarBangType :: VarBangType -> Doc
-- Slight infelicity: with print non-atomic type with parens
pprVarBangType (v, bang, t) = ppr v <+> dcolon <+> pprBangType (bang, t)

------------------------------
pprBangType :: BangType -> Doc
-- Make sure we print
--
-- Con {-# UNPACK #-} a
--
-- rather than
--
-- Con {-# UNPACK #-}a
--
-- when there's no strictness annotation. If there is a strictness annotation,
-- it's okay to not put a space between it and the type.
pprBangType (bt@(Bang _ NoSourceStrictness), t) = ppr bt <+> pprParendType t
pprBangType (bt, t) = ppr bt <> pprParendType t

------------------------------
instance Ppr Bang where
    ppr (Bang su ss) = ppr su <+> ppr ss

------------------------------
instance Ppr SourceUnpackedness where
    ppr NoSourceUnpackedness = empty
    ppr SourceNoUnpack       = text "{-# NOUNPACK #-}"
    ppr SourceUnpack         = text "{-# UNPACK #-}"

------------------------------
instance Ppr SourceStrictness where
    ppr NoSourceStrictness = empty
    ppr SourceLazy         = char '~'
    ppr SourceStrict       = char '!'

------------------------------
instance Ppr DecidedStrictness where
    ppr DecidedLazy   = empty
    ppr DecidedStrict = char '!'
    ppr DecidedUnpack = text "{-# UNPACK #-} !"

------------------------------
{-# DEPRECATED pprVarStrictType
               "As of @template-haskell-2.11.0.0@, 'VarStrictType' has been replaced by 'VarBangType'. Please use 'pprVarBangType' instead." #-}
pprVarStrictType :: (Name, Strict, Type) -> Doc
pprVarStrictType = pprVarBangType

------------------------------
{-# DEPRECATED pprStrictType
               "As of @template-haskell-2.11.0.0@, 'StrictType' has been replaced by 'BangType'. Please use 'pprBangType' instead." #-}
pprStrictType :: (Strict, Type) -> Doc
pprStrictType = pprBangType

------------------------------
pprParendType :: Type -> Doc
pprParendType (VarT v)            = pprName' Applied v
-- `Applied` is used here instead of `ppr` because of infix names (#13887)
pprParendType (ConT c)            = pprName' Applied c
pprParendType (TupleT 0)          = text "()"
pprParendType (TupleT 1)          = pprParendType (ConT (tupleTypeName 1))
pprParendType (TupleT n)          = parens (hcat (replicate (n-1) comma))
pprParendType (UnboxedTupleT n)   = hashParens $ hcat $ replicate (n-1) comma
pprParendType (UnboxedSumT arity) = hashParens $ hcat $ replicate (arity-1) bar
pprParendType ArrowT              = parens (text "->")
pprParendType ListT               = text "[]"
pprParendType (LitT l)            = pprTyLit l
pprParendType (PromotedT c)       = text "'" <> pprName' Applied c
pprParendType (PromotedTupleT 0)  = text "'()"
pprParendType (PromotedTupleT 1)  = pprParendType (PromotedT (tupleDataName 1))
pprParendType (PromotedTupleT n)  = quoteParens (hcat (replicate (n-1) comma))
pprParendType PromotedNilT        = text "'[]"
pprParendType PromotedConsT       = text "'(:)"
pprParendType StarT               = char '*'
pprParendType ConstraintT         = text "Constraint"
pprParendType (SigT ty k)         = parens (ppr ty <+> text "::" <+> ppr k)
pprParendType WildCardT           = char '_'
pprParendType (InfixT x n y)      = parens (ppr x <+> pprName' Infix n <+> ppr y)
pprParendType t@(UInfixT {})      = parens (pprUInfixT t)
pprParendType (ParensT t)         = ppr t
pprParendType tuple | (TupleT n, args) <- split tuple
                    , length args == n
                    = parens (commaSep args)
pprParendType (ImplicitParamT n t)= text ('?':n) <+> text "::" <+> ppr t
pprParendType EqualityT           = text "(~)"
pprParendType t@(ForallT {})      = parens (ppr t)
pprParendType t@(ForallVisT {})   = parens (ppr t)
pprParendType t@(AppT {})         = parens (ppr t)
pprParendType t@(AppKindT {})     = parens (ppr t)

pprUInfixT :: Type -> Doc
pprUInfixT (UInfixT x n y) = pprUInfixT x <+> pprName' Infix n <+> pprUInfixT y
pprUInfixT t               = ppr t

instance Ppr Type where
    ppr (ForallT tvars ctxt ty) = sep [pprForall tvars ctxt, ppr ty]
    ppr (ForallVisT tvars ty)   = sep [pprForallVis tvars [], ppr ty]
    ppr ty = pprTyApp (split ty)
       -- Works, in a degnerate way, for SigT, and puts parens round (ty :: kind)
       -- See Note [Pretty-printing kind signatures]
instance Ppr TypeArg where
    ppr (TANormal ty) = ppr ty
    ppr (TyArg ki) = char '@' <> ppr ki

pprParendTypeArg :: TypeArg -> Doc
pprParendTypeArg (TANormal ty) = pprParendType ty
pprParendTypeArg (TyArg ki) = char '@' <> pprParendType ki
{- Note [Pretty-printing kind signatures]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC's parser only recognises a kind signature in a type when there are
parens around it.  E.g. the parens are required here:
   f :: (Int :: *)
   type instance F Int = (Bool :: *)
So we always print a SigT with parens (see #10050). -}

pprTyApp :: (Type, [TypeArg]) -> Doc
pprTyApp (ArrowT, [TANormal arg1, TANormal arg2]) = sep [pprFunArgType arg1 <+> text "->", ppr arg2]
pprTyApp (EqualityT, [TANormal arg1, TANormal arg2]) =
    sep [pprFunArgType arg1 <+> text "~", ppr arg2]
pprTyApp (ListT, [TANormal arg]) = brackets (ppr arg)
pprTyApp (TupleT n, args)
 | length args == n
 = if n == 1
   then pprTyApp (ConT (tupleTypeName 1), args)
   else parens (commaSep args)
pprTyApp (PromotedTupleT n, args)
 | length args == n
 = if n == 1
   then pprTyApp (PromotedT (tupleDataName 1), args)
   else quoteParens (commaSep args)
pprTyApp (fun, args) = pprParendType fun <+> sep (map pprParendTypeArg args)

pprFunArgType :: Type -> Doc    -- Should really use a precedence argument
-- Everything except forall and (->) binds more tightly than (->)
pprFunArgType ty@(ForallT {})                 = parens (ppr ty)
pprFunArgType ty@(ForallVisT {})              = parens (ppr ty)
pprFunArgType ty@((ArrowT `AppT` _) `AppT` _) = parens (ppr ty)
pprFunArgType ty@(SigT _ _)                   = parens (ppr ty)
pprFunArgType ty                              = ppr ty

data ForallVisFlag = ForallVis   -- forall a -> {...}
                   | ForallInvis -- forall a.   {...}
  deriving Show

data TypeArg = TANormal Type
             | TyArg Kind

split :: Type -> (Type, [TypeArg])    -- Split into function and args
split t = go t []
    where go (AppT t1 t2) args = go t1 (TANormal t2:args)
          go (AppKindT ty ki) args = go ty (TyArg ki:args)
          go ty           args = (ty, args)

pprTyLit :: TyLit -> Doc
pprTyLit (NumTyLit n) = integer n
pprTyLit (StrTyLit s) = text (show s)

instance Ppr TyLit where
  ppr = pprTyLit

------------------------------
instance Ppr TyVarBndr where
    ppr (PlainTV nm)    = ppr nm
    ppr (KindedTV nm k) = parens (ppr nm <+> dcolon <+> ppr k)

instance Ppr Role where
    ppr NominalR          = text "nominal"
    ppr RepresentationalR = text "representational"
    ppr PhantomR          = text "phantom"
    ppr InferR            = text "_"

------------------------------
pprCxt :: Cxt -> Doc
pprCxt [] = empty
pprCxt ts = ppr_cxt_preds ts <+> text "=>"

ppr_cxt_preds :: Cxt -> Doc
ppr_cxt_preds [] = empty
ppr_cxt_preds [t@ImplicitParamT{}] = parens (ppr t)
ppr_cxt_preds [t@ForallT{}] = parens (ppr t)
ppr_cxt_preds [t] = ppr t
ppr_cxt_preds ts = parens (commaSep ts)

------------------------------
instance Ppr Range where
    ppr = brackets . pprRange
        where pprRange :: Range -> Doc
              pprRange (FromR e) = ppr e <> text ".."
              pprRange (FromThenR e1 e2) = ppr e1 <> text ","
                                        <> ppr e2 <> text ".."
              pprRange (FromToR e1 e2) = ppr e1 <> text ".." <> ppr e2
              pprRange (FromThenToR e1 e2 e3) = ppr e1 <> text ","
                                             <> ppr e2 <> text ".."
                                             <> ppr e3

------------------------------
where_clause :: [Dec] -> Doc
where_clause [] = empty
where_clause ds = nest nestDepth $ text "where" <+> vcat (map (ppr_dec False) ds)

showtextl :: Show a => a -> Doc
showtextl = text . map toLower . show

hashParens :: Doc -> Doc
hashParens d = text "(# " <> d <> text " #)"

quoteParens :: Doc -> Doc
quoteParens d = text "'(" <> d <> text ")"

-----------------------------
instance Ppr Loc where
  ppr (Loc { loc_module = md
           , loc_package = pkg
           , loc_start = (start_ln, start_col)
           , loc_end = (end_ln, end_col) })
    = hcat [ text pkg, colon, text md, colon
           , parens $ int start_ln <> comma <> int start_col
           , text "-"
           , parens $ int end_ln <> comma <> int end_col ]

-- Takes a list of printable things and prints them separated by commas followed
-- by space.
commaSep :: Ppr a => [a] -> Doc
commaSep = commaSepWith ppr

-- Takes a list of things and prints them with the given pretty-printing
-- function, separated by commas followed by space.
commaSepWith :: (a -> Doc) -> [a] -> Doc
commaSepWith pprFun = sep . punctuate comma . map pprFun

-- Takes a list of printable things and prints them separated by semicolons
-- followed by space.
semiSep :: Ppr a => [a] -> Doc
semiSep = sep . punctuate semi . map ppr

-- Prints out the series of vertical bars that wraps an expression or pattern
-- used in an unboxed sum.
unboxedSumBars :: Doc -> SumAlt -> SumArity -> Doc
unboxedSumBars d alt arity = hashParens $
    bars (alt-1) <> d <> bars (arity - alt)
  where
    bars i = hsep (replicate i bar)

-- Text containing the vertical bar character.
bar :: Doc
bar = char '|'
