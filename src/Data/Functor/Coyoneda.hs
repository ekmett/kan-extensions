{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, MPTCs, fundeps
--
-- The co-Yoneda lemma for a covariant 'Functor' @f@ states that @'Coyoneda' f@
-- is naturally isomorphic to @f@.
----------------------------------------------------------------------------
module Data.Functor.Coyoneda
  ( Coyoneda(..)
  , liftCoyoneda, lowerCoyoneda, lowerM
  -- * as a Left Kan extension
  , coyonedaToLan, lanToCoyoneda
  -- * as a Left Kan lift
  , coyonedaToLift, liftToCoyoneda
  ) where

import Control.Applicative
import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Function (on)
import Data.Functor.Adjunction
import Data.Functor.Bind
import Data.Functor.Extend
import Data.Functor.Identity
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Lift
import Data.Functor.Plus
import Data.Functor.Representable
import Data.Key
import Data.Foldable
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (sequence, lookup, zipWith)
import Text.Read hiding (lift)

-- | A covariant form suitable for Yoneda reduction
data Coyoneda f a where
  Coyoneda :: (b -> a) -> f b -> Coyoneda f a

-- | @Coyoneda f@ is the left Kan extension of @f@ along the 'Identity' functor.
--
-- @
-- 'coyonedaToLan' . 'lanToCoyoneda' ≡ 'id'
-- 'lanToCoyoneda' . 'coyonedaToLan' ≡ 'id'
-- @
coyonedaToLan :: Coyoneda f a -> Lan Identity f a
coyonedaToLan (Coyoneda ba fb) = Lan (ba . runIdentity) fb

lanToCoyoneda :: Lan Identity f a -> Coyoneda f a
lanToCoyoneda (Lan iba fb) = Coyoneda (iba . Identity) fb

{-# RULES "coyonedaToLan/lanToCoyoneda=id" coyonedaToLan . lanToCoyoneda = id #-}
{-# RULES "lanToCoyoneda/coyonedaToLan=id" lanToCoyoneda . coyonedaToLan = id #-}

-- | @'Coyoneda' f@ is the left Kan lift of @f@ along the 'Identity' functor.
--
-- @
-- 'coyonedaToLift' . 'liftToCoyoneda' ≡ 'id'
-- 'liftToCoyoneda' . 'coyonedaToLift' ≡ 'id'
-- @
coyonedaToLift :: Coyoneda f a -> Lift Identity f a
coyonedaToLift (Coyoneda ba fb) = Lift $ \ f2iz -> ba <$> runIdentity (f2iz fb)

liftToCoyoneda :: Functor f => Lift Identity f a -> Coyoneda f a
liftToCoyoneda (Lift m) = Coyoneda id (m Identity)

{-# RULES "coyonedaToLift/liftToCoyoneda=id" coyonedaToLift . liftToCoyoneda = id #-}
{-# RULES "liftToCoyoneda/coyonedaToLift=id" liftToCoyoneda . coyonedaToLift = id #-}

instance Functor (Coyoneda f) where
  fmap f (Coyoneda g v) = Coyoneda (f . g) v
  {-# INLINE fmap #-}

type instance Key (Coyoneda f) = Key f

instance Keyed f => Keyed (Coyoneda f) where
  mapWithKey f (Coyoneda k a) = Coyoneda id $ mapWithKey (\x -> f x . k) a
  {-# INLINE mapWithKey #-}

instance Apply f => Apply (Coyoneda f) where
  m <.> n = liftCoyoneda $ lowerCoyoneda m <.> lowerCoyoneda n
  {-# INLINE (<.>) #-}

instance Applicative f => Applicative (Coyoneda f) where
  pure = liftCoyoneda . pure
  {-# INLINE pure #-}
  m <*> n = liftCoyoneda $ lowerCoyoneda m <*> lowerCoyoneda n
  {-# INLINE (<*>) #-}

instance Zip f => Zip (Coyoneda f) where
  zipWith f m n = liftCoyoneda $ zipWith f (lowerCoyoneda m) (lowerCoyoneda n)
  {-# INLINE zipWith #-}

instance ZipWithKey f => ZipWithKey (Coyoneda f) where
  zipWithKey f m n = liftCoyoneda $ zipWithKey f (lowerCoyoneda m) (lowerCoyoneda n)
  {-# INLINE zipWithKey #-}

instance Alternative f => Alternative (Coyoneda f) where
  empty = liftCoyoneda empty
  {-# INLINE empty #-}
  m <|> n = liftCoyoneda $ lowerCoyoneda m <|> lowerCoyoneda n
  {-# INLINE (<|>) #-}

instance Alt f => Alt (Coyoneda f) where
  m <!> n = liftCoyoneda $ lowerCoyoneda m <!> lowerCoyoneda n
  {-# INLINE (<!>) #-}

instance Plus f => Plus (Coyoneda f) where
  zero = liftCoyoneda zero
  {-# INLINE zero #-}

instance Bind m => Bind (Coyoneda m) where
  Coyoneda f v >>- k = liftCoyoneda (v >>- lowerCoyoneda . k . f)
  {-# INLINE (>>-) #-}

instance Monad m => Monad (Coyoneda m) where
  return = Coyoneda id . return
  {-# INLINE return #-}
  Coyoneda f v >>= k = lift (v >>= lowerM . k . f)
  {-# INLINE (>>=) #-}

instance MonadTrans Coyoneda where
  lift = Coyoneda id
  {-# INLINE lift #-}

instance MonadFix f => MonadFix (Coyoneda f) where
  mfix f = lift $ mfix (lowerM . f)
  {-# INLINE mfix #-}

instance MonadPlus f => MonadPlus (Coyoneda f) where
  mzero = lift mzero
  {-# INLINE mzero #-}
  m `mplus` n = lift $ lowerM m `mplus` lowerM n
  {-# INLINE mplus #-}

instance (Functor f, Lookup f) => Lookup (Coyoneda f) where
  lookup k f = lookup k (lowerCoyoneda f)
  {-# INLINE lookup #-}

instance (Functor f, Indexable f) => Indexable (Coyoneda f) where
  index = index . lowerCoyoneda
  {-# INLINE index #-}

instance Representable f => Representable (Coyoneda f) where
  tabulate = liftCoyoneda . tabulate
  {-# INLINE tabulate #-}

instance Extend w => Extend (Coyoneda w) where
  extended k (Coyoneda f v) = Coyoneda id $ extended (k . Coyoneda f) v
  {-# INLINE extended #-}

instance Comonad w => Comonad (Coyoneda w) where
  extend k (Coyoneda f v) = Coyoneda id $ extend (k . Coyoneda f) v
  {-# INLINE extend #-}
  extract (Coyoneda f v) = f (extract v)
  {-# INLINE extract #-}

instance ComonadTrans Coyoneda where
  lower (Coyoneda f a) = fmap f a
  {-# INLINE lower #-}

instance Foldable f => Foldable (Coyoneda f) where
  foldMap f (Coyoneda k a) = foldMap (f . k) a
  {-# INLINE foldMap #-}

instance FoldableWithKey f => FoldableWithKey (Coyoneda f) where
  foldMapWithKey f (Coyoneda k a) = foldMapWithKey (\x -> f x . k) a
  {-# INLINE foldMapWithKey #-}

instance Foldable1 f => Foldable1 (Coyoneda f) where
  foldMap1 f (Coyoneda k a) = foldMap1 (f . k) a
  {-# INLINE foldMap1 #-}

instance FoldableWithKey1 f => FoldableWithKey1 (Coyoneda f) where
  foldMapWithKey1 f (Coyoneda k a) = foldMapWithKey1 (\x -> f x . k) a
  {-# INLINE foldMapWithKey1 #-}

instance Traversable f => Traversable (Coyoneda f) where
  traverse f (Coyoneda k a) = Coyoneda id <$> traverse (f . k) a
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Coyoneda f) where
  traverse1 f (Coyoneda k a) = Coyoneda id <$> traverse1 (f . k) a
  {-# INLINE traverse1 #-}

instance TraversableWithKey f => TraversableWithKey (Coyoneda f) where
  traverseWithKey f (Coyoneda k a) = Coyoneda id <$> traverseWithKey (\x -> f x . k) a
  {-# INLINE traverseWithKey #-}

instance TraversableWithKey1 f => TraversableWithKey1 (Coyoneda f) where
  traverseWithKey1 f (Coyoneda k a) = Coyoneda id <$> traverseWithKey1 (\x -> f x . k) a
  {-# INLINE traverseWithKey1 #-}

instance Distributive f => Distributive (Coyoneda f) where
  collect f = liftCoyoneda . collect (lowerCoyoneda . f)
  {-# INLINE collect #-}

instance (Functor f, Show (f a)) => Show (Coyoneda f a) where
  showsPrec d (Coyoneda f a) = showParen (d > 10) $
    showString "liftCoyoneda " . showsPrec 11 (fmap f a)
  {-# INLINE showsPrec #-}

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f a)) => Read (Coyoneda f a) where
  readPrec = parens $ prec 10 $ do
    Ident "liftCoyoneda" <- lexP
    liftCoyoneda <$> step readPrec
  {-# INLINE readPrec #-}
#endif

instance (Functor f, Eq (f a)) => Eq (Coyoneda f a) where
  (==) = (==) `on` lowerCoyoneda
  {-# INLINE (==) #-}

instance (Functor f, Ord (f a)) => Ord (Coyoneda f a) where
  compare = compare `on` lowerCoyoneda
  {-# INLINE compare #-}

instance Adjunction f g => Adjunction (Coyoneda f) (Coyoneda g) where
  unit = liftCoyoneda . fmap liftCoyoneda . unit
  {-# INLINE unit #-}
  counit = counit . fmap lowerCoyoneda . lowerCoyoneda
  {-# INLINE counit #-}

-- | Yoneda "expansion"
--
-- @
-- 'liftCoyoneda' . 'lowerCoyoneda' ≡ 'id'
-- 'lowerCoyoneda' . 'liftCoyoneda' ≡ 'id'
-- @
--
-- @
-- lowerCoyoneda (liftCoyoneda fa) = -- by definition
-- lowerCoyoneda (Coyoneda id fa)  = -- by definition
-- fmap id fa                      = -- functor law
-- fa
-- @
--
-- @
-- 'lift' = 'liftCoyoneda'
-- @
liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = Coyoneda id
{-# INLINE liftCoyoneda #-}

-- | Yoneda reduction lets us walk under the existential and apply 'fmap'.
--
-- <http://ncatlab.org/nlab/show/Yoneda+reduction>
--
-- You can view 'Coyoneda' as just the arguments to 'fmap' tupled up.
--
-- @
-- 'lower' = 'lowerM' = 'lowerCoyoneda'
-- @
lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda f m) = fmap f m
{-# INLINE lowerCoyoneda #-}

-- | Yoneda reduction given a 'Monad' lets us walk under the existential and apply 'liftM'.
--
-- You can view 'Coyoneda' as just the arguments to 'liftM' tupled up.
--
-- @
-- 'lower' = 'lowerM' = 'lowerCoyoneda'
-- @
lowerM :: Monad f => Coyoneda f a -> f a
lowerM (Coyoneda f m) = liftM f m
{-# INLINE lowerM #-}
