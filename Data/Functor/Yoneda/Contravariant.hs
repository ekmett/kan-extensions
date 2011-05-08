{-# LANGUAGE CPP, GADTs, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Yoneda.Contravariant
-- Copyright   :  (C) 2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, MPTCs, fundeps
--
----------------------------------------------------------------------------
module Data.Functor.Yoneda.Contravariant
  ( Yoneda
  , yoneda
  , liftYoneda
  , lowerYoneda
  , liftYonedaT
  , lowerYonedaT
  , lowerM
  , YonedaT(..)
  ) where

import Control.Applicative
import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fix
import Control.Monad.Representable
import Control.Monad.Trans.Class
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Function (on)
import Data.Functor.Bind
import Data.Functor.Plus
import Data.Functor.Identity
import Data.Functor.Adjunction
import Data.Key
import Prelude hiding (sequence)
import Text.Read hiding (lift)

type Yoneda = YonedaT Identity

-- | The contravariant Yoneda lemma applied to a covariant functor
data YonedaT f a where
  YonedaT :: (b -> a) -> f b -> YonedaT f a

yoneda :: (b -> a) -> b -> Yoneda a
yoneda f = YonedaT f . Identity

liftYoneda :: a -> Yoneda a 
liftYoneda = YonedaT id . Identity

lowerYoneda :: Yoneda a -> a
lowerYoneda (YonedaT f (Identity a)) = f a

liftYonedaT :: f a -> YonedaT f a 
liftYonedaT = YonedaT id

lowerYonedaT :: Functor f => YonedaT f a -> f a
lowerYonedaT (YonedaT f m) = fmap f m

lowerM :: Monad f => YonedaT f a -> f a 
lowerM (YonedaT f m) = liftM f m

instance Functor (YonedaT f) where
  fmap f (YonedaT g v) = YonedaT (f . g) v

type instance Key (YonedaT f) = Key f

instance Keyed f => Keyed (YonedaT f) where
  mapWithKey f (YonedaT k a) = YonedaT id $ mapWithKey (\x -> f x . k) a

instance Apply f => Apply (YonedaT f) where
  m <.> n = liftYonedaT $ lowerYonedaT m <.> lowerYonedaT n

instance Applicative f => Applicative (YonedaT f) where
  pure = liftYonedaT . pure
  m <*> n = liftYonedaT $ lowerYonedaT m <*> lowerYonedaT n

instance Alternative f => Alternative (YonedaT f) where
  empty = liftYonedaT empty 
  m <|> n = liftYonedaT $ lowerYonedaT m <|> lowerYonedaT n

instance Alt f => Alt (YonedaT f) where
  m <!> n = liftYonedaT $ lowerYonedaT m <!> lowerYonedaT n

instance Plus f => Plus (YonedaT f) where
  zero = liftYonedaT zero

instance Bind m => Bind (YonedaT m) where
  YonedaT f v >>- k = liftYonedaT (v >>- lowerYonedaT . k . f)

instance Monad m => Monad (YonedaT m) where
  return = YonedaT id . return
  YonedaT f v >>= k = lift (v >>= lowerM . k . f)

instance MonadTrans YonedaT where
  lift = YonedaT id

instance MonadFix f => MonadFix (YonedaT f) where
  mfix f = lift $ mfix (lowerM . f)

instance MonadPlus f => MonadPlus (YonedaT f) where
  mzero = lift mzero
  m `mplus` n = lift $ lowerM m `mplus` lowerM n

instance (Functor f, Indexable f) => Indexable (YonedaT f) where
  index = index . lowerYonedaT

instance Representable f => Representable (YonedaT f) where
  tabulate = liftYonedaT . tabulate

instance Extend w => Extend (YonedaT w) where
  extend k (YonedaT f v) = YonedaT id $ extend (k . YonedaT f) v

instance Comonad w => Comonad (YonedaT w) where
  extract (YonedaT f v) = f (extract v)

instance ComonadTrans YonedaT where
  lower (YonedaT f a) = fmap f a

instance Foldable f => Foldable (YonedaT f) where
  foldMap f (YonedaT k a) = foldMap (f . k) a

instance FoldableWithKey f => FoldableWithKey (YonedaT f) where
  foldMapWithKey f (YonedaT k a) = foldMapWithKey (\x -> f x . k) a

instance Foldable1 f => Foldable1 (YonedaT f) where
  foldMap1 f (YonedaT k a) = foldMap1 (f . k) a

instance FoldableWithKey1 f => FoldableWithKey1 (YonedaT f) where
  foldMapWithKey1 f (YonedaT k a) = foldMapWithKey1 (\x -> f x . k) a

instance Traversable f => Traversable (YonedaT f) where
  traverse f (YonedaT k a) = YonedaT id <$> traverse (f . k) a

instance Traversable1 f => Traversable1 (YonedaT f) where
  traverse1 f (YonedaT k a) = YonedaT id <$> traverse1 (f . k) a

instance TraversableWithKey f => TraversableWithKey (YonedaT f) where
  traverseWithKey f (YonedaT k a) = YonedaT id <$> traverseWithKey (\x -> f x . k) a

instance TraversableWithKey1 f => TraversableWithKey1 (YonedaT f) where
  traverseWithKey1 f (YonedaT k a) = YonedaT id <$> traverseWithKey1 (\x -> f x . k) a

instance Distributive f => Distributive (YonedaT f) where
  collect f = liftYonedaT . collect (lowerYonedaT . f)

instance (Functor f, Show (f a)) => Show (YonedaT f a) where
  showsPrec d (YonedaT f a) = showParen (d > 10) $
    showString "liftYonedaT " . showsPrec 11 (fmap f a)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f a)) => Read (YonedaT f a) where
  readPrec = parens $ prec 10 $ do
    Ident "liftYonedaT" <- lexP
    liftYonedaT <$> step readPrec
#endif

instance (Functor f, Eq (f a)) => Eq (YonedaT f a) where
  (==) = (==) `on` lowerYonedaT

instance (Functor f, Ord (f a)) => Ord (YonedaT f a) where
  compare = compare `on` lowerYonedaT

instance Adjunction f g => Adjunction (YonedaT f) (YonedaT g) where
  unit = liftYonedaT . fmap liftYonedaT . unit
  counit = counit . fmap lowerYonedaT . lowerYonedaT

