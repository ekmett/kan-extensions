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
-- Yoneda Reduction:
--
-- <http://ncatlab.org/nlab/show/Yoneda+reduction>
--
-- @'Yoneda' f@ is isomorphic to @'Lan' f 'Identity'@
----------------------------------------------------------------------------
module Data.Functor.Yoneda.Reduction
  ( Yoneda(..)
  , liftYoneda
  , lowerYoneda
  , lowerM
  ) where

import Control.Applicative
import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Function (on)
import Data.Functor.Bind
import Data.Functor.Extend
import Data.Functor.Plus
import Data.Functor.Adjunction
import Data.Functor.Representable
import Data.Key
import Data.Foldable
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (sequence, lookup, zipWith)
import Text.Read hiding (lift)

-- | A form suitable for Yoneda reduction
data Yoneda f a where
  Yoneda :: (b -> a) -> f b -> Yoneda f a

instance Functor (Yoneda f) where
  fmap f (Yoneda g v) = Yoneda (f . g) v
  {-# INLINE fmap #-}

type instance Key (Yoneda f) = Key f

instance Keyed f => Keyed (Yoneda f) where
  mapWithKey f (Yoneda k a) = Yoneda id $ mapWithKey (\x -> f x . k) a
  {-# INLINE mapWithKey #-}

instance Apply f => Apply (Yoneda f) where
  m <.> n = liftYoneda $ lowerYoneda m <.> lowerYoneda n
  {-# INLINE (<.>) #-}

instance Applicative f => Applicative (Yoneda f) where
  pure = liftYoneda . pure
  {-# INLINE pure #-}
  m <*> n = liftYoneda $ lowerYoneda m <*> lowerYoneda n
  {-# INLINE (<*>) #-}

instance Zip f => Zip (Yoneda f) where
  zipWith f m n = liftYoneda $ zipWith f (lowerYoneda m) (lowerYoneda n)
  {-# INLINE zipWith #-}

instance ZipWithKey f => ZipWithKey (Yoneda f) where
  zipWithKey f m n = liftYoneda $ zipWithKey f (lowerYoneda m) (lowerYoneda n)
  {-# INLINE zipWithKey #-}

instance Alternative f => Alternative (Yoneda f) where
  empty = liftYoneda empty
  {-# INLINE empty #-}
  m <|> n = liftYoneda $ lowerYoneda m <|> lowerYoneda n
  {-# INLINE (<|>) #-}

instance Alt f => Alt (Yoneda f) where
  m <!> n = liftYoneda $ lowerYoneda m <!> lowerYoneda n
  {-# INLINE (<!>) #-}

instance Plus f => Plus (Yoneda f) where
  zero = liftYoneda zero
  {-# INLINE zero #-}

instance Bind m => Bind (Yoneda m) where
  Yoneda f v >>- k = liftYoneda (v >>- lowerYoneda . k . f)
  {-# INLINE (>>-) #-}

instance Monad m => Monad (Yoneda m) where
  return = Yoneda id . return
  {-# INLINE return #-}
  Yoneda f v >>= k = lift (v >>= lowerM . k . f)
  {-# INLINE (>>=) #-}

instance MonadTrans Yoneda where
  lift = Yoneda id
  {-# INLINE lift #-}

instance MonadFix f => MonadFix (Yoneda f) where
  mfix f = lift $ mfix (lowerM . f)
  {-# INLINE mfix #-}

instance MonadPlus f => MonadPlus (Yoneda f) where
  mzero = lift mzero
  {-# INLINE mzero #-}
  m `mplus` n = lift $ lowerM m `mplus` lowerM n
  {-# INLINE mplus #-}

instance (Functor f, Lookup f) => Lookup (Yoneda f) where
  lookup k f = lookup k (lowerYoneda f)
  {-# INLINE lookup #-}

instance (Functor f, Indexable f) => Indexable (Yoneda f) where
  index = index . lowerYoneda
  {-# INLINE index #-}

instance Representable f => Representable (Yoneda f) where
  tabulate = liftYoneda . tabulate
  {-# INLINE tabulate #-}

instance Extend w => Extend (Yoneda w) where
  extended k (Yoneda f v) = Yoneda id $ extended (k . Yoneda f) v
  {-# INLINE extended #-}

instance Comonad w => Comonad (Yoneda w) where
  extend k (Yoneda f v) = Yoneda id $ extend (k . Yoneda f) v
  {-# INLINE extend #-}
  extract (Yoneda f v) = f (extract v)
  {-# INLINE extract #-}

instance ComonadTrans Yoneda where
  lower (Yoneda f a) = fmap f a
  {-# INLINE lower #-}

instance Foldable f => Foldable (Yoneda f) where
  foldMap f (Yoneda k a) = foldMap (f . k) a
  {-# INLINE foldMap #-}

instance FoldableWithKey f => FoldableWithKey (Yoneda f) where
  foldMapWithKey f (Yoneda k a) = foldMapWithKey (\x -> f x . k) a
  {-# INLINE foldMapWithKey #-}

instance Foldable1 f => Foldable1 (Yoneda f) where
  foldMap1 f (Yoneda k a) = foldMap1 (f . k) a
  {-# INLINE foldMap1 #-}

instance FoldableWithKey1 f => FoldableWithKey1 (Yoneda f) where
  foldMapWithKey1 f (Yoneda k a) = foldMapWithKey1 (\x -> f x . k) a
  {-# INLINE foldMapWithKey1 #-}

instance Traversable f => Traversable (Yoneda f) where
  traverse f (Yoneda k a) = Yoneda id <$> traverse (f . k) a
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Yoneda f) where
  traverse1 f (Yoneda k a) = Yoneda id <$> traverse1 (f . k) a
  {-# INLINE traverse1 #-}

instance TraversableWithKey f => TraversableWithKey (Yoneda f) where
  traverseWithKey f (Yoneda k a) = Yoneda id <$> traverseWithKey (\x -> f x . k) a
  {-# INLINE traverseWithKey #-}

instance TraversableWithKey1 f => TraversableWithKey1 (Yoneda f) where
  traverseWithKey1 f (Yoneda k a) = Yoneda id <$> traverseWithKey1 (\x -> f x . k) a
  {-# INLINE traverseWithKey1 #-}

instance Distributive f => Distributive (Yoneda f) where
  collect f = liftYoneda . collect (lowerYoneda . f)
  {-# INLINE collect #-}

instance (Functor f, Show (f a)) => Show (Yoneda f a) where
  showsPrec d (Yoneda f a) = showParen (d > 10) $
    showString "liftYoneda " . showsPrec 11 (fmap f a)
  {-# INLINE showsPrec #-}

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f a)) => Read (Yoneda f a) where
  readPrec = parens $ prec 10 $ do
    Ident "liftYoneda" <- lexP
    liftYoneda <$> step readPrec
  {-# INLINE readPrec #-}
#endif

instance (Functor f, Eq (f a)) => Eq (Yoneda f a) where
  (==) = (==) `on` lowerYoneda
  {-# INLINE (==) #-}

instance (Functor f, Ord (f a)) => Ord (Yoneda f a) where
  compare = compare `on` lowerYoneda
  {-# INLINE compare #-}

instance Adjunction f g => Adjunction (Yoneda f) (Yoneda g) where
  unit = liftYoneda . fmap liftYoneda . unit
  {-# INLINE unit #-}
  counit = counit . fmap lowerYoneda . lowerYoneda
  {-# INLINE counit #-}

-- | Yoneda "expansion"
--
-- @
-- 'liftYoneda' . 'lowerYoneda' ≡ 'id'
-- 'lowerYoneda' . 'liftYoneda' ≡ 'id'
-- @
--
--
-- @
-- 'lift' = 'liftYoneda'
-- @
liftYoneda :: f a -> Yoneda f a
liftYoneda = Yoneda id
{-# INLINE liftYoneda #-}

-- | Yoneda reduction
--
-- @
-- 'lower' = 'lowerM' = 'lowerYoneda'
-- @
lowerYoneda :: Functor f => Yoneda f a -> f a
lowerYoneda (Yoneda f m) = fmap f m
{-# INLINE lowerYoneda #-}

-- | Yoneda reduction given a 'Monad'.
--
-- @
-- 'lower' = 'lowerM' = 'lowerYoneda'
-- @
lowerM :: Monad f => Yoneda f a -> f a
lowerM (Yoneda f m) = liftM f m
{-# INLINE lowerM #-}
