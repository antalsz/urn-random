{-# OPTIONS_HADDOCK not-home #-}

module Data.Urn.Common (
  -- * Types
  Urn(), Weight, MonadSample(),
  -- * 'Urn' properties
  size, totalWeight,
  -- * Constructing 'Urn's
  singleton,
  fromList, fromNonEmpty,
  -- * Inserting into 'Urn's
  insert, addToUrn
) where

import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Foldable
import Data.Coerce

import Data.Urn.MonadSample
import Data.Urn.Internal hiding (size)
import qualified Data.Urn.Internal as Internal

size :: Urn a -> Word
size = (coerce :: (Urn a -> Size) -> (Urn a -> Word)) Internal.size
{-# INLINABLE size #-}

totalWeight :: Urn a -> Weight
totalWeight = weight . wtree
{-# INLINABLE totalWeight #-}

singleton :: Weight -> a -> Urn a
singleton w a = Urn { Internal.size = 1, wtree = WLeaf w a }
{-# INLINABLE singleton #-}

addToUrn :: Foldable t => Urn a -> t (Weight, a) -> Urn a
addToUrn = foldl' (flip $ uncurry insert)
{-# INLINABLE addToUrn #-}

fromList :: [(Weight,a)] -> Maybe (Urn a)
fromList = fmap fromNonEmpty . nonEmpty
{-# INLINABLE fromList #-}

fromNonEmpty :: NonEmpty (Weight,a) -> Urn a
-- fromNonEmpty ((w,t):|wts) = addToUrn (singleton w t) wts
fromNonEmpty = Internal.construct  -- this is O(n) now
{-# INLINABLE fromNonEmpty #-}
