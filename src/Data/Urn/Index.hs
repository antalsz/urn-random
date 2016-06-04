-- TODO: 'remove' is wrong!!!

{-# OPTIONS_HADDOCK not-home #-}

module Data.Urn.Index (
  -- * Types
  Urn(), Index(), Weight(), RandomWord(),
  -- * Constructing 'Urn's
  singleton, fromList, fromNonEmpty,
  -- * Constructing indices
  randomIndex,
  -- * Sampling
  sample,
  remove,
  -- * Updating
  insert,
  update, replace,
  -- * Other functions
  addToUrn,
  -- * 'Urn' properties
  size, totalWeight
) where

import Data.Urn.Common

import Data.Urn.RandomWord
import qualified Data.Urn.Internal as Internal
import Data.Urn.Internal (Urn(Urn), Index(..))

randomIndex :: RandomWord m => Urn a -> m Index
randomIndex = Internal.randomIndexWith randomWord
{-# INLINABLE randomIndex #-}

sample :: Urn a -> Index -> a
sample = Internal.sample . Internal.wtree

remove :: Urn a -> Index -> (Weight, a, Maybe (Urn a))
remove t i = case Internal.uninsert t of
               (w', a', Just t')   -> case replace w' a' t' i of
                                        (w'', a'', t'') -> (w'', a'', Just t'')
               res@(_, _, Nothing) -> res

update :: (Weight -> a -> (Weight, a)) -> Urn a -> Index -> (Weight, a, Weight, a, Urn a)
update upd (Urn size wt) i =
  case Internal.update upd wt i of
    (wOld, aOld, wNew, aNew, wt') -> (wOld, aOld, wNew, aNew, Urn size wt')

replace :: Weight -> a -> Urn a -> Index -> (Weight, a, Urn a)
replace wNew aNew (Urn size wt) i = case Internal.replace wNew aNew wt i of
                                      (w', a', wt') -> (w', a', Urn size wt')
