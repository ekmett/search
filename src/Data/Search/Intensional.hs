{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Search.Intensional
  ( Search(..)
  , pessimumM
  , optimum, pessimum
  , optimalScore, pessimalScore
  , cps
  , union
  , pair
  , fromList
  -- *  Hilbert's epsilon
  , Hilbert(..)
  , best, worst
  , bestScore, worstScore
  -- * Boolean-valued search
  , every
  , exists
  ) where

import Control.Applicative
import Control.Monad.Trans.Cont
import Control.Monad (ap)
import Data.Function (on)
import Data.Functor.Alt
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Int
import Data.Monoid
import Data.Ord
import Data.Profunctor
import Data.Proxy
import Data.Tagged
import Data.Typeable
import Data.Word
import GHC.Generics

-- | Given a test that is required to execute in finite time for _all_ inputs, even infinite ones,
-- 'Search' should productively yield an answer.
--
-- I currently also assume that comparison of scores can be done in finite time for all scores.
--
-- This rules out large score sets.
--
-- @'Search' 'Bool'@ can be used for predicate searches.
newtype Search a b = Search { optimumM :: forall m. (Monad m, Applicative m) => (b -> m a) -> m b }
  deriving Typeable

optimum :: Search a b -> (b -> a) -> b
optimum (Search k) f = runIdentity $ k (Identity . f)

-- | Find the worst-scoring result of a search with monadic effects.
pessimumM :: (Monad m, Applicative m) => Search (Down a) b -> (b -> m a) -> m b
pessimumM = optimumM . lmap Down

-- | Find the worst-scoring result of a search.
pessimum :: Search (Down a) b -> (b -> a) -> b
pessimum = optimum . lmap Down

instance Profunctor Search where
  dimap f g (Search k) = Search $ \p -> fmap g $ k $ fmap f . p . g
  {-# INLINE dimap #-}

instance Functor (Search a) where
  fmap f (Search k) = Search $ \p -> fmap f $ k $ p . f
  {-# INLINE fmap #-}

instance Apply (Search a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance Applicative (Search a) where
  pure a = Search $ \_ -> return a
  (<*>) = ap

instance Ord a => Alt (Search a) where
  Search l <!> Search r = Search $ \p -> do
    (a,b) <- (,) <$> l p <*> r p
    (\ma mb -> if ma >= mb then a else b) <$> p a <*> p b

instance Bind (Search a) where
  (>>-) = (>>=)

instance Monad (Search a) where
  return a = Search $ \_ -> return a
  m >>= k = jn (fmap k m) where
    jn x = Search $ \p -> do
      z <- optimumM x $ \ y -> optimumM y p >>= p
      optimumM z p

-- | <http://en.wikipedia.org/wiki/Epsilon_calculus#Hilbert_notation Hilbert's epsilon>
class Hilbert a b where
  epsilon :: Search a b
  default epsilon :: (GHilbert a (Rep b), Generic b) => Search a b
  epsilon = to <$> gepsilon

-- | Generic derivation of Hilbert's epsilon.
class GHilbert a f where
  gepsilon :: Search a (f b)

instance GHilbert a U1 where
  gepsilon = pure U1

instance (GHilbert a f, GHilbert a g) => GHilbert a (f :*: g) where
  gepsilon = liftA2 (:*:) gepsilon gepsilon

instance (GHilbert a f, GHilbert a g, Ord a) => GHilbert a (f :+: g) where
  gepsilon = L1 <$> gepsilon <!> R1 <$> gepsilon

instance Hilbert a b => GHilbert a (K1 i b) where
  gepsilon = K1 <$> epsilon

instance GHilbert a f => GHilbert a (M1 i c f) where
  gepsilon = M1 <$> gepsilon

instance Hilbert x ()
instance Hilbert x (Proxy a) where epsilon = pure Proxy
instance Hilbert x a => Hilbert x (Tagged s a) where epsilon = Tagged <$> epsilon
instance (Hilbert x a, Hilbert x b) => Hilbert x (a, b)
instance (Hilbert x a, Hilbert x b, Hilbert x c) => Hilbert x (a, b, c)
instance (Hilbert x a, Hilbert x b, Hilbert x c, Hilbert x d) => Hilbert x (a, b, c, d)
instance (Hilbert x a, Hilbert x b, Hilbert x c, Hilbert x d, Hilbert x e) => Hilbert x (a, b, c, d, e)
instance Ord x => Hilbert x Bool
instance Ord x => Hilbert x Any where epsilon = Any <$> epsilon
instance Ord x => Hilbert x All where epsilon = All <$> epsilon
instance Hilbert x a => Hilbert x (Product a) where epsilon = Product <$> epsilon
instance Hilbert x a => Hilbert x (Sum a) where epsilon = Sum <$> epsilon
instance Ord x => Hilbert x Ordering
instance Ord x => Hilbert x Char where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Int8 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Int16 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Word8 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Word16 where epsilon = fromList [minBound .. maxBound]
instance (Ord x, Hilbert x a) => Hilbert x [a]
instance (Ord x, Hilbert x a) => Hilbert x (ZipList a) where epsilon = ZipList <$> epsilon
instance (Ord x, Hilbert x a) => Hilbert x (Maybe a)
instance (Ord x, Hilbert x a) => Hilbert x (First a) where epsilon = First <$> epsilon
instance (Ord x, Hilbert x a) => Hilbert x (Last a) where epsilon = Last <$> epsilon
instance (Ord x, Hilbert x a, Hilbert x b) => Hilbert x (Either a b)
instance (Ord x, Ord a, Hilbert x b) => Hilbert x (Search a b) where
  epsilon = fromList <$> epsilon

-- | What is the best score obtained by the search?
optimalScore :: Search a b -> (b -> a) -> a
optimalScore m p = p (optimum m p)

-- | What is the worst score obtained by the search?
pessimalScore :: Search (Down a) b -> (b -> a) -> a
pessimalScore m p = p (pessimum m p)

-- | search for an optimal answer using Hilbert's epsilon
--
-- >>> search (>4) :: Int8
-- 5
best :: Hilbert a b => (b -> a) -> b
best = optimum epsilon

-- | What is the worst scoring answer by Hilbert's epsilon?
worst :: Hilbert (Down a) b => (b -> a) -> b
worst = pessimum epsilon

bestScore :: Hilbert a b => (b -> a) -> a
bestScore = optimalScore epsilon

worstScore :: Hilbert (Down a) b => (b -> a) -> a
worstScore = pessimalScore epsilon

-- | does there exist an element satisfying the predicate?
--
-- >>> exists (>(maxBound::Int8))
-- False
--
exists :: Hilbert Bool b => (b -> Bool) -> Bool
exists = bestScore

every :: Hilbert Bool b => (b -> Bool) -> Bool
every p = not.p $ best $ not.p

union :: Ord a => Search a b -> Search a b -> Search a b
union = (<!>)

pair :: Ord a => b -> b -> Search a b
pair = on (<!>) pure

fromList :: Ord a => [b] -> Search a b
fromList = foldr1 (<!>) . map return

-- | 'Search' is more powerful than 'Cont'.
--
-- This provides a canonical monad homomorphism into 'Cont'.
cps :: Search a b -> Cont a b
cps = cont . optimalScore
