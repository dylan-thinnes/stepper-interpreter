{-# LANGUAGE FlexibleInstances, Safe #-}

-- | Monadic front-end to Text.PrettyPrint

module Ppr.Lib (

        -- * The document type
        Doc,            -- Abstract, instance of Show
        PprM,

        -- * Annotation
        mannotate,

        -- * Primitive Documents
        empty,
        semi, comma, colon, dcolon, space, equals, arrow,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace,

        -- * Converting values into documents
        text, char, ptext,
        int, integer, float, double, rational,

        -- * Wrapping documents in delimiters
        parens, brackets, braces, quotes, doubleQuotes,

        -- * Combining documents
        (<>), (<+>), hcat, hsep,
        ($$), ($+$), vcat,
        sep, cat,
        fsep, fcat,
        nest,
        hang, punctuate,

        -- * Predicates on documents
        isEmpty,

    to_HPJ_Doc, pprName, pprName'
  ) where


import Language.Haskell.TH.Syntax
    (Uniq, Name(..), showName', NameFlavour(..), NameIs(..))
import qualified Text.PrettyPrint.Annotated as HPJ
import Control.Monad (liftM, liftM2, ap)
import Ppr.THLibMapCopy ( Map )
import qualified Ppr.THLibMapCopy as Map ( lookup, insert, empty )
import Prelude hiding ((<>))

infixl 6 <>
infixl 6 <+>
infixl 5 $$, $+$

mannotate :: Maybe a -> Doc a -> Doc a
mannotate (Just a) = fmap $ HPJ.annotate a
mannotate Nothing = id

-- ---------------------------------------------------------------------------
-- The interface

-- The primitive Doc values

instance Show (Doc a) where
   show d = HPJ.render (to_HPJ_Doc d)

isEmpty :: Doc a    -> PprM Bool;  -- ^ Returns 'True' if the document is empty

empty   :: Doc a;                 -- ^ An empty document
semi    :: Doc a;                 -- ^ A ';' character
comma   :: Doc a;                 -- ^ A ',' character
colon   :: Doc a;                 -- ^ A ':' character
dcolon  :: Doc a;                 -- ^ A "::" string
space   :: Doc a;                 -- ^ A space character
equals  :: Doc a;                 -- ^ A '=' character
arrow   :: Doc a;                 -- ^ A "->" string
lparen  :: Doc a;                 -- ^ A '(' character
rparen  :: Doc a;                 -- ^ A ')' character
lbrack  :: Doc a;                 -- ^ A '[' character
rbrack  :: Doc a;                 -- ^ A ']' character
lbrace  :: Doc a;                 -- ^ A '{' character
rbrace  :: Doc a;                 -- ^ A '}' character

text     :: String   -> Doc a
ptext    :: String   -> Doc a
char     :: Char     -> Doc a
int      :: Int      -> Doc a
integer  :: Integer  -> Doc a
float    :: Float    -> Doc a
double   :: Double   -> Doc a
rational :: Rational -> Doc a


parens       :: Doc a -> Doc a;     -- ^ Wrap document in @(...)@
brackets     :: Doc a -> Doc a;     -- ^ Wrap document in @[...]@
braces       :: Doc a -> Doc a;     -- ^ Wrap document in @{...}@
quotes       :: Doc a -> Doc a;     -- ^ Wrap document in @\'...\'@
doubleQuotes :: Doc a -> Doc a;     -- ^ Wrap document in @\"...\"@

-- Combining @Doc a@ values

(<>)   :: Doc a -> Doc a -> Doc a;     -- ^Beside
hcat   :: [Doc a] -> Doc a;          -- ^List version of '<>'
(<+>)  :: Doc a -> Doc a -> Doc a;     -- ^Beside, separated by space
hsep   :: [Doc a] -> Doc a;          -- ^List version of '<+>'

($$)   :: Doc a -> Doc a -> Doc a;     -- ^Above; if there is no
                                 -- overlap it \"dovetails\" the two
($+$)  :: Doc a -> Doc a -> Doc a;     -- ^Above, without dovetailing.
vcat   :: [Doc a] -> Doc a;          -- ^List version of '$$'

cat    :: [Doc a] -> Doc a;          -- ^ Either hcat or vcat
sep    :: [Doc a] -> Doc a;          -- ^ Either hsep or vcat
fcat   :: [Doc a] -> Doc a;          -- ^ \"Paragraph fill\" version of cat
fsep   :: [Doc a] -> Doc a;          -- ^ \"Paragraph fill\" version of sep

nest   :: Int -> Doc a -> Doc a;     -- ^ Nested


-- GHC-specific ones.

hang :: Doc a -> Int -> Doc a -> Doc a;      -- ^ @hang d1 n d2 = sep [d1, nest n d2]@
punctuate :: Doc a -> [Doc a] -> [Doc a]
   -- ^ @punctuate p [d1, ... dn] = [d1 \<> p, d2 \<> p, ... dn-1 \<> p, dn]@

-- ---------------------------------------------------------------------------
-- The "implementation"

type State = (Map Name Name, Uniq)
data PprM a = PprM { runPprM :: State -> (a, State) }

pprName :: Name -> Doc a
pprName = pprName' Alone

pprName' :: NameIs -> Name -> Doc a
pprName' ni n@(Name o (NameU _))
 = PprM $ \s@(fm, i)
        -> let (n', s') = case Map.lookup n fm of
                         Just d -> (d, s)
                         Nothing -> let n'' = Name o (NameU i)
                                    in (n'', (Map.insert n n'' fm, i + 1))
           in (HPJ.text $ showName' ni n', s')
pprName' ni n = text $ showName' ni n

{-
instance Show Name where
  show (Name occ (NameU u))    = occString occ ++ "_" ++ show (I# u)
  show (Name occ NameS)        = occString occ
  show (Name occ (NameG ns m)) = modString m ++ "." ++ occString occ

data Name = Name OccName NameFlavour

data NameFlavour
  | NameU Int#                  -- A unique local name
-}

to_HPJ_Doc :: Doc a -> HPJ.Doc a
to_HPJ_Doc d = fst $ runPprM d (Map.empty, 0)

instance Functor PprM where
      fmap = liftM

instance Applicative PprM where
      pure x = PprM $ \s -> (x, s)
      (<*>) = ap

instance Monad PprM where
    m >>= k  = PprM $ \s -> let (x, s') = runPprM m s
                            in runPprM (k x) s'

type Doc a = PprM (HPJ.Doc a)

-- The primitive Doc values

isEmpty = liftM HPJ.isEmpty

empty = return HPJ.empty
semi = return HPJ.semi
comma = return HPJ.comma
colon = return HPJ.colon
dcolon = return $ HPJ.text "::"
space = return HPJ.space
equals = return HPJ.equals
arrow = return $ HPJ.text "->"
lparen = return HPJ.lparen
rparen = return HPJ.rparen
lbrack = return HPJ.lbrack
rbrack = return HPJ.rbrack
lbrace = return HPJ.lbrace
rbrace = return HPJ.rbrace

text = return . HPJ.text
ptext = return . HPJ.ptext
char = return . HPJ.char
int = return . HPJ.int
integer = return . HPJ.integer
float = return . HPJ.float
double = return . HPJ.double
rational = return . HPJ.rational


parens = liftM HPJ.parens
brackets = liftM HPJ.brackets
braces = liftM HPJ.braces
quotes = liftM HPJ.quotes
doubleQuotes = liftM HPJ.doubleQuotes

-- Combining @Doc@ values

(<>) = liftM2 (HPJ.<>)
hcat = liftM HPJ.hcat . sequence
(<+>) = liftM2 (HPJ.<+>)
hsep = liftM HPJ.hsep . sequence

($$) = liftM2 (HPJ.$$)
($+$) = liftM2 (HPJ.$+$)
vcat = liftM HPJ.vcat . sequence

cat  = liftM HPJ.cat . sequence
sep  = liftM HPJ.sep . sequence
fcat = liftM HPJ.fcat . sequence
fsep = liftM HPJ.fsep . sequence

nest n = liftM (HPJ.nest n)

hang d1 n d2 = do d1' <- d1
                  d2' <- d2
                  return (HPJ.hang d1' n d2')

-- punctuate uses the same definition as Text.PrettyPrint
punctuate _ []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d' [] = [d']
                     go d' (e:es) = (d' <> p) : go e es

