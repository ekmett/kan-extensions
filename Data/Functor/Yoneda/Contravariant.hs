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
import Data.Functor.Plus
import Data.Functor.Adjunction
import Data.Functor.Representable
import Data.Key
import Prelude hiding (sequence, lookup)
import Text.Read hiding (lift)

-- | The contravariant Yoneda lemma applied to a covariant functor
data Yoneda f a where
  Yoneda :: (b -> a) -> f b -> Yoneda f a

liftYoneda :: f a -> Yoneda f a 
liftYoneda = Yoneda id

lowerYoneda :: Functor f => Yoneda f a -> f a
lowerYoneda (Yoneda f m) = fmap f m

lowerM :: Monad f => Yoneda f a -> f a 
lowerM (Yoneda f m) = liftM f m

instance Functor (Yoneda f) where
  fmap f (Yoneda g v) = Yoneda (f . g) v

type instance Key (Yoneda f) = Key f

instance Keyed f => Keyed (Yoneda f) where
  mapWithKey f (Yoneda k a) = Yoneda id $ mapWithKey (\x -> f x . k) a

instance Apply f => Apply (Yoneda f) where
  m <.> n = liftYoneda $ lowerYoneda m <.> lowerYoneda n

instance Applicative f => Applicative (Yoneda f) where
  pure = liftYoneda . pure
  m <*> n = liftYoneda $ lowerYoneda m <*> lowerYoneda n

instance Alternative f => Alternative (Yoneda f) where
  empty = liftYoneda empty 
  m <|> n = liftYoneda $ lowerYoneda m <|> lowerYoneda n

instance Alt f => Alt (Yoneda f) where
  m <!> n = liftYoneda $ lowerYoneda m <!> lowerYoneda n

instance Plus f => Plus (Yoneda f) where
  zero = liftYoneda zero

instance Bind m => Bind (Yoneda m) where
  Yoneda f v >>- k = liftYoneda (v >>- lowerYoneda . k . f)

instance Monad m => Monad (Yoneda m) where
  return = Yoneda id . return
  Yoneda f v >>= k = lift (v >>= lowerM . k . f)

instance MonadTrans Yoneda where
  lift = Yoneda id

instance MonadFix f => MonadFix (Yoneda f) where
  mfix f = lift $ mfix (lowerM . f)

instance MonadPlus f => MonadPlus (Yoneda f) where
  mzero = lift mzero
  m `mplus` n = lift $ lowerM m `mplus` lowerM n

instance (Functor f, Lookup f) => Lookup (Yoneda f) where
  lookup k f = lookup k (lowerYoneda f)

instance (Functor f, Indexable f) => Indexable (Yoneda f) where
  index = index . lowerYoneda

instance Representable f => Representable (Yoneda f) where
  tabulate = liftYoneda . tabulate

instance Extend w => Extend (Yoneda w) where
  extend k (Yoneda f v) = Yoneda id $ extend (k . Yoneda f) v

instance Comonad w => Comonad (Yoneda w) where
  extract (Yoneda f v) = f (extract v)

instance ComonadTrans Yoneda where
  lower (Yoneda f a) = fmap f a

instance Foldable f => Foldable (Yoneda f) where
  foldMap f (Yoneda k a) = foldMap (f . k) a

instance FoldableWithKey f => FoldableWithKey (Yoneda f) where
  foldMapWithKey f (Yoneda k a) = foldMapWithKey (\x -> f x . k) a

instance Foldable1 f => Foldable1 (Yoneda f) where
  foldMap1 f (Yoneda k a) = foldMap1 (f . k) a

instance FoldableWithKey1 f => FoldableWithKey1 (Yoneda f) where
  foldMapWithKey1 f (Yoneda k a) = foldMapWithKey1 (\x -> f x . k) a

instance Traversable f => Traversable (Yoneda f) where
  traverse f (Yoneda k a) = Yoneda id <$> traverse (f . k) a

instance Traversable1 f => Traversable1 (Yoneda f) where
  traverse1 f (Yoneda k a) = Yoneda id <$> traverse1 (f . k) a

instance TraversableWithKey f => TraversableWithKey (Yoneda f) where
  traverseWithKey f (Yoneda k a) = Yoneda id <$> traverseWithKey (\x -> f x . k) a

instance TraversableWithKey1 f => TraversableWithKey1 (Yoneda f) where
  traverseWithKey1 f (Yoneda k a) = Yoneda id <$> traverseWithKey1 (\x -> f x . k) a

instance Distributive f => Distributive (Yoneda f) where
  collect f = liftYoneda . collect (lowerYoneda . f)

instance (Functor f, Show (f a)) => Show (Yoneda f a) where
  showsPrec d (Yoneda f a) = showParen (d > 10) $
    showString "liftYoneda " . showsPrec 11 (fmap f a)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f a)) => Read (Yoneda f a) where
  readPrec = parens $ prec 10 $ do
    Ident "liftYoneda" <- lexP
    liftYoneda <$> step readPrec
#endif

instance (Functor f, Eq (f a)) => Eq (Yoneda f a) where
  (==) = (==) `on` lowerYoneda

instance (Functor f, Ord (f a)) => Ord (Yoneda f a) where
  compare = compare `on` lowerYoneda

instance Adjunction f g => Adjunction (Yoneda f) (Yoneda g) where
  unit = liftYoneda . fmap liftYoneda . unit
  counit = counit . fmap lowerYoneda . lowerYoneda

