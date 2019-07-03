{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
#include "kan-extensions-common.h"

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, MPTCs, fundeps
--
-- @'Coyoneda' f@ is the "free functor" over @f@.
-- The co-Yoneda lemma for a covariant 'Functor' @f@ states that @'Coyoneda' f@
-- is naturally isomorphic to @f@.
----------------------------------------------------------------------------
module Data.Functor.Coyoneda
  ( Coyoneda(..)
  , liftCoyoneda, lowerCoyoneda, lowerM, hoistCoyoneda
  -- * as a Left Kan extension
  , coyonedaToLan, lanToCoyoneda
  ) where

import Control.Applicative as A
import Control.Monad (MonadPlus(..), liftM)
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
#if !LIFTED_FUNCTOR_CLASSES
import Data.Function (on)
#endif
import Data.Functor.Adjunction
import Data.Functor.Bind
import Data.Functor.Classes
import Data.Functor.Extend
import Data.Functor.Identity
import Data.Functor.Kan.Lan
import Data.Functor.Plus
import Data.Functor.Rep
import Data.Foldable
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (sequence, lookup, zipWith)
import Text.Read hiding (lift)

-- | A covariant 'Functor' suitable for Yoneda reduction
--
data Coyoneda f a where
  Coyoneda :: (b -> a) -> f b -> Coyoneda f a

-- | @Coyoneda f@ is the left Kan extension of @f@ along the 'Identity' functor.
--
-- @Coyoneda f@ is always a functor, even if @f@ is not. In this case, it
-- is called the /free functor over @f@/. Note the following categorical fine
-- print: If @f@ is not a functor, @Coyoneda f@ is actually not the left Kan
-- extension of @f@ along the 'Identity' functor, but along the inclusion
-- functor from the discrete subcategory of /Hask/ which contains only identity
-- functions as morphisms to the full category /Hask/. (This is because @f@,
-- not being a proper functor, can only be interpreted as a categorical functor
-- by restricting the source category to only contain identities.)
--
-- @
-- 'coyonedaToLan' . 'lanToCoyoneda' ≡ 'id'
-- 'lanToCoyoneda' . 'coyonedaToLan' ≡ 'id'
-- @
coyonedaToLan :: Coyoneda f a -> Lan Identity f a
coyonedaToLan (Coyoneda ba fb) = Lan (ba . runIdentity) fb
{-# INLINE coyonedaToLan #-}

lanToCoyoneda :: Lan Identity f a -> Coyoneda f a
lanToCoyoneda (Lan iba fb) = Coyoneda (iba . Identity) fb
{-# INLINE lanToCoyoneda #-}

-- {-# RULES "coyonedaToLan/lanToCoyoneda=id" coyonedaToLan . lanToCoyoneda = id #-}
-- {-# RULES "lanToCoyoneda/coyonedaToLan=id" lanToCoyoneda . coyonedaToLan = id #-}

instance Functor (Coyoneda f) where
  fmap f (Coyoneda g v) = Coyoneda (f . g) v
  {-# INLINE fmap #-}

instance Apply f => Apply (Coyoneda f) where
  Coyoneda mf m <.> Coyoneda nf n =
    liftCoyoneda $ (\mres nres -> mf mres (nf nres)) <$> m <.> n
  {-# INLINE (<.>) #-}
  Coyoneda _ m .> Coyoneda g n = Coyoneda g (m .> n)
  {-# INLINE (.>) #-}
  Coyoneda f m <. Coyoneda _ n = Coyoneda f (m <. n)
  {-# INLINE (<.) #-}

instance Applicative f => Applicative (Coyoneda f) where
  pure = liftCoyoneda . pure
  {-# INLINE pure #-}
  Coyoneda mf m <*> Coyoneda nf n =
    liftCoyoneda $ (\mres nres -> mf mres (nf nres)) <$> m <*> n
  {-# INLINE (<*>) #-}
  Coyoneda _ m *> Coyoneda g n = Coyoneda g (m *> n)
  {-# INLINE (*>) #-}
  Coyoneda f m <* Coyoneda _ n = Coyoneda f (m <* n)
  {-# INLINE (<*) #-}

instance Alternative f => Alternative (Coyoneda f) where
  empty = liftCoyoneda empty
  {-# INLINE empty #-}
  m <|> n = liftCoyoneda $ lowerCoyoneda m <|> lowerCoyoneda n
  {-# INLINE (<|>) #-}
  some = liftCoyoneda . A.some . lowerCoyoneda
  {-# INLINE some #-}
  many = liftCoyoneda . A.many . lowerCoyoneda
  {-# INLINE many #-}

{-
-- These are slightly optimized versions of the *default*
-- `some` and `many` definitions for `Coyoneda`. I don't
-- know if it's worth the clutter to expose them.
someDefault (Coyoneda vf vb) = liftCoyoneda some_v
  where
    many_v = some_v <|> pure []
    some_v = (:) . vf <$> vb <*> many_v
{-# INLINE someDefault #-}

manyDefault (Coyoneda vf vb) = liftCoyoneda many_v
  where
    many_v = some_v <|> pure []
    some_v = (:) . vf <$> vb <*> many_v
{-# INLINE many #-}
-}

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
#if __GLASGOW_HASKELL__ < 710
  -- pre-AMP
  return = Coyoneda id . return
  {-# INLINE return #-}

  Coyoneda _ m >> Coyoneda g n = Coyoneda g (m >> n)
  {-# INLINE (>>) #-}
#else
  -- post-AMP
  (>>) = (*>)
  {-# INLINE (>>) #-}
#endif
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

instance Representable f => Representable (Coyoneda f) where
  type Rep (Coyoneda f) = Rep f
  tabulate = liftCoyoneda . tabulate
  {-# INLINE tabulate #-}
  index = index . lowerCoyoneda
  {-# INLINE index #-}

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

instance Foldable1 f => Foldable1 (Coyoneda f) where
  foldMap1 f (Coyoneda k a) = foldMap1 (f . k) a
  {-# INLINE foldMap1 #-}

instance Traversable f => Traversable (Coyoneda f) where
  traverse f (Coyoneda k a) = Coyoneda id <$> traverse (f . k) a
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Coyoneda f) where
  traverse1 f (Coyoneda k a) = Coyoneda id <$> traverse1 (f . k) a
  {-# INLINE traverse1 #-}

instance Distributive f => Distributive (Coyoneda f) where
  collect f = liftCoyoneda . collect (lowerCoyoneda . f)
  {-# INLINE collect #-}

instance (Functor f, Show1 f) => Show1 (Coyoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftShowsPrec sp sl d (Coyoneda f a) =
    showsUnaryWith (liftShowsPrec sp sl) "liftCoyoneda" d (fmap f a)
  {-# INLINE liftShowsPrec #-}
#else
  showsPrec1 d (Coyoneda f a) = showParen (d > 10) $
    showString "liftCoyoneda " . showsPrec1 11 (fmap f a)
  {-# INLINE showsPrec1 #-}
#endif

instance (Read1 f) => Read1 (Coyoneda f) where
#if LIFTED_FUNCTOR_CLASSES
  liftReadsPrec rp rl = readsData $
    readsUnaryWith (liftReadsPrec rp rl) "liftCoyoneda" liftCoyoneda
  {-# INLINE liftReadsPrec #-}
#else
  readsPrec1 d = readParen (d > 10) $ \r' ->
    [ (liftCoyoneda f, t)
    | ("liftCoyoneda", s) <- lex r'
    , (f, t) <- readsPrec1 11 s
    ]
  {-# INLINE readsPrec1 #-}
#endif

instance (Functor f, Show1 f, Show a) => Show (Coyoneda f a) where
  showsPrec = showsPrec1
  {-# INLINE showsPrec #-}

instance Read (f a) => Read (Coyoneda f a) where
#ifdef __GLASGOW_HASKELL__
  readPrec = parens $ prec 10 $ do
    Ident "liftCoyoneda" <- lexP
    liftCoyoneda <$> step readPrec
  {-# INLINE readPrec #-}
#else
  readsPrec d = readParen (d > 10) $ \r' ->
    [ (liftCoyoneda f, t)
    | ("liftCoyoneda", s) <- lex r'
    , (f, t) <- readsPrec 11 s
    ]
  {-# INLINE readsPrec #-}
#endif

#if LIFTED_FUNCTOR_CLASSES
instance Eq1 f => Eq1 (Coyoneda f) where
  liftEq eq (Coyoneda f xs) (Coyoneda g ys) =
    liftEq (\x y -> eq (f x) (g y)) xs ys
  {-# INLINE liftEq #-}
#else
instance (Functor f, Eq1 f) => Eq1 (Coyoneda f) where
  eq1 = eq1 `on` lowerCoyoneda
  {-# INLINE eq1 #-}
#endif

#if LIFTED_FUNCTOR_CLASSES
instance Ord1 f => Ord1 (Coyoneda f) where
  liftCompare cmp (Coyoneda f xs) (Coyoneda g ys) =
    liftCompare (\x y -> cmp (f x) (g y)) xs ys
  {-# INLINE liftCompare #-}
#else
instance (Functor f, Ord1 f) => Ord1 (Coyoneda f) where
  compare1 = compare1 `on` lowerCoyoneda
  {-# INLINE compare1 #-}
#endif

instance (Functor f, Eq1 f, Eq a) => Eq (Coyoneda f a) where
  (==) = eq1
  {-# INLINE (==) #-}

instance (Functor f, Ord1 f, Ord a) => Ord (Coyoneda f a) where
  compare = compare1
  {-# INLINE compare #-}

instance Adjunction f g => Adjunction (Coyoneda f) (Coyoneda g) where
  unit = liftCoyoneda . leftAdjunct liftCoyoneda
  {-# INLINE unit #-}
  counit = rightAdjunct lowerCoyoneda . lowerCoyoneda
  {-# INLINE counit #-}

-- | Yoneda \"expansion\"
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
-- Mnemonically, \"Yoneda reduction\" sounds like and works a bit like β-reduction.
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

-- | Lift a natural transformation from @f@ to @g@ to a natural transformation
-- from @Coyoneda f@ to @Coyoneda g@.
hoistCoyoneda :: (forall a. f a -> g a) -> (Coyoneda f b -> Coyoneda g b)
hoistCoyoneda f (Coyoneda g x) = Coyoneda g (f x)
{-# INLINE hoistCoyoneda #-}
