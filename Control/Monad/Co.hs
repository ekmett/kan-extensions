{-# LANGUAGE Rank2Types
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , MultiParamTypeClasses #-}
{-# LANGUAGE ImplicitParams #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Co
-- Copyright   :  (C) 2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism)
--
-- Monads from Comonads
--
-- http://comonad.com/reader/2011/monads-from-comonads/
--
----------------------------------------------------------------------------
module Control.Monad.Co 
  ( 
  -- * Monads from Comonads
    Co, co, runCo
  -- * Monad Transformers from Comonads
  , CoT(..)
  -- * Klesili from CoKleisli
  , liftCoT0, lowerCoT0, lowerCo0
  , liftCoT1, lowerCoT1, lowerCo1
  , posW, peekW, peeksW
  , askW, asksW, traceW
  )where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Env.Class as Env
import Control.Comonad.Traced.Class as Traced
import Control.Comonad.Store.Class
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class as Reader
import Control.Monad.State.Class
import Control.Monad.Writer.Class as Writer
import Control.Monad.Identity
import Data.Functor.Bind

type Co w = CoT w Identity

co :: Functor w => (forall r. w (a -> r) -> r) -> Co w a
co f = CoT (Identity . f . fmap (fmap runIdentity))

runCo :: Functor w => Co w a -> w (a -> r) -> r
runCo m = runIdentity . runCoT m . fmap (fmap Identity)

newtype CoT w m a = CoT { runCoT :: forall r. w (a -> m r) -> m r }

instance Functor w => Functor (CoT w m) where
  fmap f (CoT w) = CoT (w . fmap (. f))

instance Extend w => Apply (CoT w m) where
  mf <.> ma = mf >>- \f -> fmap f ma

instance Extend w => Bind (CoT w m) where
  CoT k >>- f = CoT (k . extend (\wa a -> runCoT (f a) wa))

instance Comonad w => Applicative (CoT w m) where
  pure a = CoT (`extract` a)
  mf <*> ma = mf >>= \f -> fmap f ma
  
instance Comonad w => Monad (CoT w m) where
  return a = CoT (`extract` a)
  CoT k >>= f = CoT (k . extend (\wa a -> runCoT (f a) wa))

instance Comonad w => MonadTrans (CoT w) where
  lift m = CoT (extract . fmap (m >>=))

instance (Comonad w, MonadIO m) => MonadIO (CoT w m) where
  liftIO = lift . liftIO

liftCoT0 :: Comonad w => (forall a. w a -> s) -> CoT w m s
liftCoT0 f = CoT (extract <*> f)

lowerCoT0 :: (Functor w, Monad m) => CoT w m s -> w a -> m s
lowerCoT0 m = runCoT m . (return <$) 

lowerCo0 :: Functor w => Co w s -> w a -> s
lowerCo0 m = runIdentity . runCoT m . (return <$) 

liftCoT1 :: (forall a. w a -> a) -> CoT w m ()
liftCoT1 f = CoT (`f` ())

lowerCoT1 :: (Functor w, Monad m) => CoT w m () -> w a -> m a
lowerCoT1 m = runCoT m . fmap (const . return)

lowerCo1 :: Functor w => Co w () -> w a -> a
lowerCo1 m = runIdentity . runCoT m . fmap (const . return)

posW :: (ComonadStore s w, Monad m) => CoT w m s
posW = liftCoT0 pos

peekW :: (ComonadStore s w, Monad m) => s -> CoT w m ()
peekW s = liftCoT1 (peek s)

peeksW :: (ComonadStore s w, Monad m) => (s -> s) -> CoT w m ()
peeksW f = liftCoT1 (peeks f)

askW :: (ComonadEnv e w, Monad m) => CoT w m e
askW = liftCoT0 (Env.ask)

asksW :: (ComonadEnv e w, Monad m) => (e -> a) -> CoT w m a
asksW f = liftCoT0 (Env.asks f)

traceW :: (ComonadTraced e w, Monad m) => e -> CoT w m ()
traceW e = liftCoT1 (Traced.trace e)

instance (Comonad w, MonadReader e m) => MonadReader e (CoT w m) where
  ask = lift Reader.ask
  local f m = CoT (local f . runCoT m)

instance (Comonad w, MonadState s m) => MonadState s (CoT w m) where
  get = lift get
  put = lift . put

instance (Comonad w, MonadWriter e m) => MonadWriter e (CoT w m) where
  tell = lift . tell
  pass m = CoT (pass . runCoT m . fmap aug) where 
    aug f (a,e) = liftM (\r -> (r,e)) (f a)
  listen = error "Control.Monad.Co.listen: TODO"
