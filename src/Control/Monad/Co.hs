{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif
#if __GLASGOW_HASKELL__ >= 702 && __GLASGOW_HASKELL__ < 710
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism)
--
-- Monads from Comonads
--
-- <http://comonad.com/reader/2011/monads-from-comonads/>
--
-- 'Co' can be viewed as a right Kan lift along a 'Comonad'.
--
-- In general you can \"sandwich\" a monad in between two halves of an adjunction.
-- That is to say, if you have an adjunction @F -| G : C -> D @ then not only does @GF@
-- form a monad, but @GMF@ forms a monad for @M@ a monad in @D@. Therefore if we
-- have an adjunction @F -| G : Hask -> Hask^op@ then we can lift a 'Comonad' in @Hask@
-- which is a 'Monad' in @Hask^op@ to a 'Monad' in 'Hask'.
--
-- For any @r@, the 'Contravariant' functor / presheaf @(-> r)@ :: Hask^op -> Hask is adjoint to the \"same\"
-- 'Contravariant' functor @(-> r) :: Hask -> Hask^op@. So we can sandwich a
-- Monad in Hask^op in the middle to obtain @w (a -> r-) -> r+@, and then take a coend over
-- @r@ to obtain @forall r. w (a -> r) -> r@. This gives rise to 'Co'. If we observe that
-- we didn't care what the choices we made for @r@ were to finish this construction, we can
-- upgrade to @forall r. w (a -> m r) -> m r@ in a manner similar to how @ContT@ is constructed
-- yielding 'CoT'.
--
-- We could consider unifying the definition of 'Co' and 'Rift', but
-- there are many other arguments for which 'Rift' can form a 'Monad', and this
-- wouldn't give rise to 'CoT'.
----------------------------------------------------------------------------
module Control.Monad.Co
  (
  -- * Monads from Comonads
    Co, co, runCo
  -- * Monad Transformers from Comonads
  , CoT(..)
  -- * Klesili from CoKleisli
  , liftCoT0, liftCoT0M, lowerCoT0, lowerCo0
  , liftCoT1, liftCoT1M, lowerCoT1, lowerCo1
  , diter, dctrlM
  , posW, peekW, peeksW
  , askW, asksW, traceW
  )where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Comonad
import Control.Comonad.Cofree
import Control.Comonad.Density
import Control.Comonad.Env.Class as Env
import Control.Comonad.Store.Class
import Control.Comonad.Traced.Class as Traced
import Control.Monad.Error.Class
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.Reader.Class as Reader
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Writer.Class as Writer
import Data.Functor.Bind
import Data.Functor.Extend

type Co w = CoT w Identity

co :: Functor w => (forall r. w (a -> r) -> r) -> Co w a
co f = CoT (Identity . f . fmap (fmap runIdentity))

runCo :: Functor w => Co w a -> w (a -> r) -> r
runCo m = runIdentity . runCoT m . fmap (fmap Identity)

-- |
-- @
-- 'Co' w a ~ 'Data.Functor.Kan.Rift.Rift' w 'Identity' a
-- @
newtype CoT w m a = CoT { runCoT :: forall r. w (a -> m r) -> m r }

instance Functor w => Functor (CoT w m) where
  fmap f (CoT w) = CoT (w . fmap (. f))

instance Extend w => Apply (CoT w m) where
  mf <.> ma = mf >>- \f -> fmap f ma

instance Extend w => Bind (CoT w m) where
  CoT k >>- f = CoT (k . extended (\wa a -> runCoT (f a) wa))

instance Comonad w => Applicative (CoT w m) where
  pure a = CoT (`extract` a)
  mf <*> ma = mf >>= \f -> fmap f ma

instance Comonad w => Monad (CoT w m) where
  return = pure
  CoT k >>= f = CoT (k . extend (\wa a -> runCoT (f a) wa))

instance (Comonad w, Fail.MonadFail m) => Fail.MonadFail (CoT w m) where
  fail msg = CoT $ \ _ -> Fail.fail msg

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

posW :: ComonadStore s w => CoT w m s
posW = liftCoT0 pos

peekW :: ComonadStore s w => s -> CoT w m ()
peekW s = liftCoT1 (peek s)

peeksW :: ComonadStore s w => (s -> s) -> CoT w m ()
peeksW f = liftCoT1 (peeks f)

askW :: ComonadEnv e w => CoT w m e
askW = liftCoT0 (Env.ask)

asksW :: ComonadEnv e w => (e -> a) -> CoT w m a
asksW f = liftCoT0 (Env.asks f)

traceW :: ComonadTraced e w => e -> CoT w m ()
traceW e = liftCoT1 (Traced.trace e)

liftCoT0M :: (Comonad w, Monad m) => (forall a. w a -> m s) -> CoT w m s
liftCoT0M f = CoT (\wa -> extract wa =<< f wa)

liftCoT1M :: Monad m => (forall a. w a -> m a) -> CoT w m ()
liftCoT1M f = CoT (($ ()) <=< f)

diter :: Functor f => a -> (a -> f a) -> Density (Cofree f) a
diter x y = liftDensity . coiter y $ x

dctrlM :: Monad m => (forall a. w a -> m (w a)) -> CoT (Density w) m ()
dctrlM k = liftCoT1M (\(Density w a) -> liftM w (k a))

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

instance (Comonad w, MonadError e m) => MonadError e (CoT w m) where
  throwError = lift . throwError
  catchError = error "Control.Monad.Co.catchError: TODO"
