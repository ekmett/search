{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Search
  ( Search(..)
  , pessimum
  , union
  , pair
  , fromList
  , best, bestScore
  , worst, worstScore
  -- * Boolean-valued search
  , every
  , exists
  -- *  Hilbert's epsilon
  , Hilbert(..)
  ) where

import Control.Applicative
import Data.Function (on)
import Data.Functor.Alt
import Data.Functor.Bind
import Data.Int
import Data.Monoid
import Data.Ord
import Data.Profunctor
import Data.Proxy
import Data.Tagged
import Data.Word
import GHC.Generics

-- | Given a test that is required to execute in finite time for _all_ inputs, even infinite ones,
-- 'Search' should productively yield an answer.
--
-- @'Search Bool'@ can be used to answer predicate searches.
newtype Search a b = Search { optimum :: (b -> a) -> b }

-- | Find the worst-scoring result of a search.
pessimum :: Search (Down a) b -> (b -> a) -> b
pessimum = optimum . lmap Down

instance Profunctor Search where
  dimap f g (Search k) = Search $ \ba -> g (k (f.ba.g))
  {-# INLINE dimap #-}

instance Functor (Search a) where
  fmap f (Search k) = Search $ \ba -> f (k (ba.f))
  {-# INLINE fmap #-}

instance Apply (Search a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance Applicative (Search a) where
  pure b = Search $ \_ -> b
  fs <*> as = Search $ \p ->
    let go q = q $ optimum as (p.q)
    in  go $ optimum fs (p.go)

instance Ord a => Alt (Search a) where
  l <!> r = Search go where
    go p
      | p a >= p b = a
      | otherwise  = b
      where
        a = optimum l p
        b = optimum r p

instance Bind (Search a) where
  Search ma >>- f = Search $ \p ->
    optimum (f (ma (\a -> p (optimum (f a) p)))) p

instance Monad (Search a) where
  return a = Search $ \_ -> a
  Search ma >>= f = Search $ \p ->
    optimum (f (ma (\a -> p (optimum (f a) p)))) p

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
instance Ord x => Hilbert x Any
instance Ord x => Hilbert x All
instance Hilbert x a => Hilbert x (Product a)
instance Hilbert x a => Hilbert x (Sum a)
instance Ord x => Hilbert x Ordering
instance Ord x => Hilbert x Char where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Int8 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Int16 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Word8 where epsilon = fromList [minBound .. maxBound]
instance Ord x => Hilbert x Word16 where epsilon = fromList [minBound .. maxBound]
instance (Ord x, Hilbert x a) => Hilbert x [a]
instance (Ord x, Hilbert x a) => Hilbert x (Maybe a)
instance (Ord x, Hilbert x a, Hilbert x b) => Hilbert x (Either a b)
instance (Ord x, Ord a, Hilbert x b) => Hilbert x (Search a b) where
  epsilon = fromList <$> epsilon

-- | search for an optimal answer using Hilbert's epsilon
--
-- >>> search (>4) :: Int8
-- 5
best :: Hilbert a b => (b -> a) -> b
best = optimum epsilon

-- | What is the worst scoring answer by Hilbert's epsilon?
worst :: Hilbert (Down a) b => (b -> a) -> b
worst = pessimum epsilon

-- | does there exist an element satisfying the predicate?
--
-- >>> exists (>(maxBound::Int8))
-- False
--
exists :: Hilbert Bool b => (b -> Bool) -> Bool
exists p = p (best p)

every :: Hilbert Bool b => (b -> Bool) -> Bool
every p = not.p $ best $ not.p

-- | What is the best score obtained by the search?
bestScore :: Search a b -> (b -> a) -> a
bestScore m p = p (optimum m p)

-- | What is the worst score obtained by the search?
worstScore :: Search (Down a) b -> (b -> a) -> a
worstScore m p = p (pessimum m p)

union :: Ord a => Search a b -> Search a b -> Search a b
union = (<!>)

pair :: Ord a => b -> b -> Search a b
pair = on (<!>) pure

fromList :: Ord a => [b] -> Search a b
fromList = foldr1 (<!>) . map return
