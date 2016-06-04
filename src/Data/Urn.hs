{-# LANGUAGE TupleSections #-}

module Data.Urn (
  -- * Types
  Urn,
  Weight,
  RandomWord,
  -- * Construction
  singleton, fromList, fromNonEmpty,
  -- * Sampling
  sample, sampleM,
  remove, removeM,
  -- * Updating
  insert,
  update, replace,
  -- * Other functions
  frequency,
  addToUrn,
  -- * 'Urn' properties
  size, totalWeight
) where

import Data.Urn.Common
import Data.Urn.Index (randomIndex)
import qualified Data.Urn.Index as Index

sample :: RandomWord m => Urn a -> m a
sample u = Index.sample u <$> randomIndex u

sampleM :: RandomWord m => Urn (m a) -> m a
sampleM u = Index.sample u =<< randomIndex u

remove :: RandomWord m => Urn a -> m (Weight, a, Maybe (Urn a))
remove u = Index.remove u <$> randomIndex u

removeM :: RandomWord m => Urn (m a) -> m (Weight, a, Maybe (Urn (m a)))
removeM u = do (w,ma,mu) <- remove u
               (w,  ,mu) <$> ma

update :: RandomWord m
       => (Weight -> a -> (Weight, a))
       -> Urn a
       -> m (Weight, a, Weight, a, Urn a)
update upd u = Index.update upd u <$> randomIndex u

replace :: RandomWord m => Weight -> a -> Urn a -> m (Weight, a, Urn a)
replace w a u = Index.replace w a u <$> randomIndex u

frequency :: RandomWord m => [(Weight, m a)] -> m a
frequency = maybe (error "Data.Urn.frequency used with empty list") sampleM . fromList
