{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
#include "kan-extensions-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Yoneda
-- Copyright   :  (C) 2011-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The covariant form of the Yoneda lemma states that @f@ is naturally
-- isomorphic to @Yoneda f@.
--
-- This is described in a rather intuitive fashion by Dan Piponi in
--
-- <http://blog.sigfpe.com/2006/11/yoneda-lemma.html>
----------------------------------------------------------------------------

module Data.Functor.Yoneda
  ( Yoneda(..)
  , liftYoneda, lowerYoneda
  , maxF, minF, maxM, minM
  -- * as a right Kan extension
  , yonedaToRan, ranToYoneda
  ) where

import Control.Applicative
import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fix
import Control.Monad.Free.Class
import Control.Monad.Trans.Class
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Foldable
import Data.Functor.Adjunction
import Data.Functor.Bind
import Data.Functor.Classes
import Data.Functor.Extend
import Data.Functor.Identity
import Data.Functor.Kan.Ran
import Data.Functor.Plus
import Data.Functor.Rep
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Traversable
import Text.Read hiding (lift)
import Prelude hiding (sequence, lookup, zipWith)

-- | @Yoneda f a@ can be viewed as the partial application of 'fmap' to its second argument.
newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

-- | The natural isomorphism between @f@ and @'Yoneda' f@ given by the Yoneda lemma
-- is witnessed by 'liftYoneda' and 'lowerYoneda'
--
-- @
-- 'liftYoneda' . 'lowerYoneda' ≡ 'id'
-- 'lowerYoneda' . 'liftYoneda' ≡ 'id'
-- @
--
-- @
-- lowerYoneda (liftYoneda fa) =         -- definition
-- lowerYoneda (Yoneda (\f -> fmap f a)) -- definition
-- (\f -> fmap f fa) id                  -- beta reduction
-- fmap id fa                            -- functor law
-- fa
-- @
--
-- @
-- 'lift' = 'liftYoneda'
-- @
liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda a = Yoneda (\f -> fmap f a)
{-# INLINE liftYoneda #-}

lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda f) = f id
{-# INLINE lowerYoneda #-}

-- TODO: coerce
-- {-# RULES "lower/lift=id" liftYoneda . lowerYoneda = id #-}
-- {-# RULES "lift/lower=id" lowerYoneda . liftYoneda = id #-}

-- | @Yoneda f@ can be viewed as the right Kan extension of @f@ along the 'Identity' functor.
--
-- @
-- 'yonedaToRan' . 'ranToYoneda' ≡ 'id'
-- 'ranToYoneda' . 'yonedaToRan' ≡ 'id'
-- @
yonedaToRan :: Yoneda f a -> Ran Identity f a
yonedaToRan (Yoneda m) = Ran (m . fmap runIdentity)
{-# INLINE yonedaToRan #-}

ranToYoneda :: Ran Identity f a -> Yoneda f a
ranToYoneda (Ran m) = Yoneda (m . fmap Identity)
{-# INLINE ranToYoneda #-}

-- {-# RULES "yonedaToRan/ranToYoneda=id" yonedaToRan . ranToYoneda = id #-}
-- {-# RULES "ranToYoneda/yonedaToRan=id" ranToYoneda . yonedaToRan = id #-}

instance Functor (Yoneda f) where
  fmap f m = Yoneda (\k -> runYoneda m (k . f))
  {-# INLINE fmap #-}

instance Apply f => Apply (Yoneda f) where
  Yoneda m <.> Yoneda n = Yoneda (\f -> m (f .) <.> n id)
  {-# INLINE (<.>) #-}

instance Applicative f => Applicative (Yoneda f) where
  pure a = Yoneda (\f -> pure (f a))
  {-# INLINE pure #-}
  Yoneda m <*> Yoneda n = Yoneda (\f -> m (f .) <*> n id)
  {-# INLINE (<*>) #-}

instance Foldable f => Foldable (Yoneda f) where
  foldMap f = foldMap f . lowerYoneda
  {-# INLINE foldMap #-}

instance Foldable1 f => Foldable1 (Yoneda f) where
  foldMap1 f = foldMap1 f . lowerYoneda
  {-# INLINE foldMap1 #-}

instance Traversable f => Traversable (Yoneda f) where
  traverse f = fmap liftYoneda . traverse f . lowerYoneda
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Yoneda f) where
  traverse1 f = fmap liftYoneda . traverse1 f . lowerYoneda
  {-# INLINE traverse1 #-}

instance Distributive f => Distributive (Yoneda f) where
  collect f = liftYoneda . collect (lowerYoneda . f)
  {-# INLINE collect #-}

instance Representable g => Representable (Yoneda g) where
  type Rep (Yoneda g) = Rep g
  tabulate = liftYoneda . tabulate
  {-# INLINE tabulate #-}
  index = index . lowerYoneda
  {-# INLINE index #-}

instance Adjunction f g => Adjunction (Yoneda f) (Yoneda g) where
  unit = liftYoneda . fmap liftYoneda . unit
  {-# INLINE unit #-}
  counit (Yoneda m) = counit (m lowerYoneda)
  {-# INLINE counit #-}

instance Show1 f => Show1 (Yoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftShowsPrec sp sl d (Yoneda f) =
    showsUnaryWith (liftShowsPrec sp sl) "liftYoneda" d (f id)
#else
  showsPrec1 d (Yoneda f) = showParen (d > 10) $
    showString "liftYoneda " . showsPrec1 11 (f id)
#endif

instance (Read1 f, Functor f) => Read1 (Yoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftReadsPrec rp rl = readsData $
    readsUnaryWith (liftReadsPrec rp rl) "liftYoneda" liftYoneda
#else
  readsPrec1 d = readParen (d > 10) $ \r' ->
    [ (liftYoneda f, t)
    | ("liftYoneda", s) <- lex r'
    , (f, t) <- readsPrec1 11 s
    ]
#endif

instance Show (f a) => Show (Yoneda f a) where
  showsPrec d (Yoneda f) = showParen (d > 10) $
    showString "liftYoneda " . showsPrec 11 (f id)

instance (Functor f, Read (f a)) => Read (Yoneda f a) where
#ifdef __GLASGOW_HASKELL__
  readPrec = parens $ prec 10 $ do
     Ident "liftYoneda" <- lexP
     liftYoneda <$> step readPrec
#else
  readsPrec d = readParen (d > 10) $ \r' ->
    [ (liftYoneda f, t)
    | ("liftYoneda", s) <- lex r'
    , (f, t) <- readsPrec 11 s
    ]
#endif

infixl 0 `on1`
on1 :: (g a -> g b -> c) -> (forall x. f x -> g x) -> f a -> f b -> c
(.*.) `on1` f = \x y -> f x .*. f y

instance Eq1 f => Eq1 (Yoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftEq eq = liftEq eq `on1` lowerYoneda
  {-# INLINE liftEq #-}
#else
  eq1 = eq1 `on1` lowerYoneda
  {-# INLINE eq1 #-}
#endif

instance Ord1 f => Ord1 (Yoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftCompare cmp = liftCompare cmp `on1` lowerYoneda
  {-# INLINE liftCompare #-}
#else
  compare1 = compare1 `on1` lowerYoneda
  {-# INLINE compare1 #-}
#endif

instance (Eq1 f, Eq a) => Eq (Yoneda f a) where
  (==) = eq1
  {-# INLINE (==) #-}

instance (Ord1 f, Ord a) => Ord (Yoneda f a) where
  compare = compare1
  {-# INLINE compare #-}

maxF :: (Functor f, Ord (f a)) => Yoneda f a -> Yoneda f a -> Yoneda f a
Yoneda f `maxF` Yoneda g = liftYoneda $ f id `max` g id
-- {-# RULES "max/maxF" max = maxF #-}
{-# INLINE maxF #-}

minF :: (Functor f, Ord (f a)) => Yoneda f a -> Yoneda f a -> Yoneda f a
Yoneda f `minF` Yoneda g = liftYoneda $ f id `max` g id
-- {-# RULES "min/minF" min = minF #-}
{-# INLINE minF #-}

maxM :: (Monad m, Ord (m a)) => Yoneda m a -> Yoneda m a -> Yoneda m a
Yoneda f `maxM` Yoneda g = lift $ f id `max` g id
-- {-# RULES "max/maxM" max = maxM #-}
{-# INLINE maxM #-}

minM :: (Monad m, Ord (m a)) => Yoneda m a -> Yoneda m a -> Yoneda m a
Yoneda f `minM` Yoneda g = lift $ f id `min` g id
-- {-# RULES "min/minM" min = minM #-}
{-# INLINE minM #-}

instance Alt f => Alt (Yoneda f) where
  Yoneda f <!> Yoneda g = Yoneda (\k -> f k <!> g k)
  {-# INLINE (<!>) #-}

instance Plus f => Plus (Yoneda f) where
  zero = Yoneda $ const zero
  {-# INLINE zero #-}

instance Alternative f => Alternative (Yoneda f) where
  empty = Yoneda $ const empty
  {-# INLINE empty #-}
  Yoneda f <|> Yoneda g = Yoneda (\k -> f k <|> g k)
  {-# INLINE (<|>) #-}

instance Bind m => Bind (Yoneda m) where
  Yoneda m >>- k = Yoneda (\f -> m id >>- \a -> runYoneda (k a) f)
  {-# INLINE (>>-) #-}

instance Monad m => Monad (Yoneda m) where
#if __GLASGOW_HASKELL__ < 710
  return a = Yoneda (\f -> return (f a))
  {-# INLINE return #-}
#endif
  Yoneda m >>= k = Yoneda (\f -> m id >>= \a -> runYoneda (k a) f)
  {-# INLINE (>>=) #-}

instance MonadFix m => MonadFix (Yoneda m) where
  mfix f = lift $ mfix (lowerYoneda . f)
  {-# INLINE mfix #-}

instance MonadPlus m => MonadPlus (Yoneda m) where
  mzero = Yoneda (const mzero)
  {-# INLINE mzero #-}
  Yoneda f `mplus` Yoneda g = Yoneda (\k -> f k `mplus` g k)
  {-# INLINE mplus #-}

instance MonadTrans Yoneda where
  lift a = Yoneda (\f -> liftM f a)
  {-# INLINE lift #-}

instance (Functor f, MonadFree f m) => MonadFree f (Yoneda m) where
  wrap = lift . wrap . fmap lowerYoneda
  {-# INLINE wrap #-}

instance Extend w => Extend (Yoneda w) where
  extended k (Yoneda m) = Yoneda (\f -> extended (f . k . liftYoneda) (m id))
  {-# INLINE extended #-}

instance Comonad w => Comonad (Yoneda w) where
  extend k (Yoneda m) = Yoneda (\f -> extend (f . k . liftYoneda) (m id))
  {-# INLINE extend #-}
  extract = extract . lowerYoneda
  {-# INLINE extract #-}

instance ComonadTrans Yoneda where
  lower = lowerYoneda
  {-# INLINE lower #-}
