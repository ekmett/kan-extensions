{-# LANGUAGE Rank2Types, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Codensity
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism)
--
----------------------------------------------------------------------------
module Control.Monad.Codensity
  ( Codensity(..)
  , lowerCodensity
  , codensityToAdjunction
  , adjunctionToCodensity
  , improve
  ) where

import Control.Applicative
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Free.Class
import Control.Monad.Free
import Control.Monad (ap, MonadPlus(..))
import Data.Functor.Adjunction
import Data.Functor.Apply
import Data.Functor.Plus
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Concurrent.Speculation
import Control.Concurrent.Speculation.Class

newtype Codensity m a = Codensity { runCodensity :: forall b. (a -> m b) -> m b }

instance MonadSpec (Codensity m) where
  specByM f g a = Codensity $ \k -> specBy f g k a
  specByM' f g a = Codensity $ \k -> specBy' f g k a

instance Functor (Codensity k) where
  fmap f (Codensity m) = Codensity (\k -> m (k . f))

instance Apply (Codensity f) where
  (<.>) = ap

instance Applicative (Codensity f) where
  pure x = Codensity (\k -> k x)
  (<*>) = ap

instance Monad (Codensity f) where
  return x = Codensity (\k -> k x)
  m >>= k = Codensity (\c -> runCodensity m (\a -> runCodensity (k a) c))

instance MonadIO m => MonadIO (Codensity m) where
  liftIO = lift . liftIO 

instance MonadTrans Codensity where
  lift m = Codensity (m >>=)

instance Alt v => Alt (Codensity v) where
  Codensity m <!> Codensity n = Codensity (\k -> m k <!> n k)

instance Plus v => Plus (Codensity v) where
  zero = Codensity (const zero)

{-
instance Plus v => Alternative (Codensity v) where
  empty = zero
  (<|>) = (<!>)

instance Plus v => MonadPlus (Codensity v) where
  mzero = zero
  mplus = (<!>)
-}

instance Alternative v => Alternative (Codensity v) where
  empty                         = Codensity (\_ -> empty)
  Codensity m <|> Codensity n = Codensity (\k -> m k <|> n k)

instance MonadPlus v => MonadPlus (Codensity v) where
  mzero                             = Codensity (\_ -> mzero)
  Codensity m `mplus` Codensity n = Codensity (\k -> m k `mplus` n k)

lowerCodensity :: Monad m => Codensity m a -> m a
lowerCodensity a = runCodensity a return

codensityToAdjunction :: Adjunction f g => Codensity g a -> g (f a)
codensityToAdjunction r = runCodensity r unit

adjunctionToCodensity :: Adjunction f g => g (f a) -> Codensity g a
adjunctionToCodensity f = Codensity (\a -> fmap (rightAdjunct a) f)

instance (Functor f, MonadFree f m) => MonadFree f (Codensity m) where
  wrap t = Codensity (\h -> wrap (fmap (\p -> runCodensity p h) t))

instance MonadReader r m => MonadState r (Codensity m) where
  get = Codensity (ask >>=)
  put s = Codensity (\k -> local (const s) (k ()))

-- | Right associate all binds in a computation that generates a free monad
-- This can improve the asymptotic efficiency of the result, while preserving
-- semantics.
improve :: Functor f => (forall m. MonadFree f m => m a) -> Free f a
improve m = lowerCodensity m

