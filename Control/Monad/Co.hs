{-# LANGUAGE Rank2Types
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , UndecidableInstances #-}
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
  ( Co(..)
  , lift0, lift1
  , lower0, lower1
  )where

import Control.Comonad
import Control.Applicative
import Control.Comonad.Store.Class
import Control.Monad.State.Class
import Data.Functor.Bind

-- import Control.Comonad.Env.Class as Env
-- import Control.Comonad.Traced.Class as Traced
-- import Control.Monad.Reader.Class
-- import Control.Monad.Writer.Class

newtype Co w a = Co { runCo :: forall r. w (a -> r) -> r }

instance Functor w => Functor (Co w) where
   fmap f (Co w) = Co (w . fmap (. f))

instance Extend w => Apply (Co w) where
   mf <.> ma = mf >>- (`fmap` ma)

instance Extend w => Bind (Co w) where
   Co k >>- f = Co (k . extend (\wa a -> runCo (f a) wa))

instance Comonad w => Applicative (Co w) where
   mf <*> ma = mf >>= (`fmap` ma)
   pure a = Co (`extract` a)

instance Comonad w => Monad (Co w) where
   return a = Co (`extract` a)
   Co k >>= f = Co (k . extend (\wa a -> runCo (f a) wa))

lift0 :: Comonad w => (forall a. w a -> s) -> Co w s
lift0 f = Co (extract <*> f)

lower0 :: Functor w => Co w s -> w a -> s
lower0 (Co f) w = f (id <$ w)

lift1 :: (forall a. w a -> a) -> Co w ()
lift1 f = Co (`f` ())

lower1 :: Functor w => Co w () -> w a -> a
lower1 (Co f) w = f (fmap const w)

instance ComonadStore s m => MonadState s (Co m) where
   get = lift0 pos
   put s = lift1 (peek s)
