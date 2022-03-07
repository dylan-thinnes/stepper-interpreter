{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Utils where

import Control.Monad
import Control.Applicative
import Language.Haskell.TH.Syntax (Name (..), OccName (..))

-- mtl
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

-- transformers
import Control.Monad.Trans.Maybe

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd :: (a, b, c) -> c
thd (_, _, c) = c

infixl 4 <$$>
(<$$>) :: Functor f => f (a -> b) -> a -> f b
(<$$>) fab a = ($ a) <$> fab

-- th
rawName :: Name -> String
rawName (Name (OccName str) _) = str

-- ERRORS
type Failable m = FailZero (MaybeT m)
newtype FailZero m a = FailZero { runFailZero :: (m a) }

liftFail :: Monad m => m a -> Failable m a
liftFail = lift . lift

runFailable :: Failable m a -> m (Maybe a)
runFailable = runMaybeT . runFailZero

runFailableDef :: Functor m => a -> Failable m a -> m a
runFailableDef a = fmap (maybe a id) . runFailable

deriving instance Functor m => Functor (FailZero m)
deriving instance Applicative m => Applicative (FailZero m)
deriving instance Monad m => Monad (FailZero m)
deriving instance Alternative m => Alternative (FailZero m)
deriving instance MonadReader r m => MonadReader r (FailZero m)
deriving instance MonadState s m => MonadState s (FailZero m)
deriving instance MonadWriter w m => MonadWriter w (FailZero m)
instance MonadTrans FailZero where
    lift = FailZero
instance MonadPlus m => MonadFail (FailZero m) where
    fail _ = lift mzero
