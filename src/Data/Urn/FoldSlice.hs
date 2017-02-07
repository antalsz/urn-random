{-# language LambdaCase, MagicHash, TypeApplications, GADTs, RankNTypes, ScopedTypeVariables, PartialTypeSignatures, RecordWildCards #-}

module FoldSlice where

import Data.Monoid
import Data.Foldable
import Data.Function
import Control.Arrow
import Data.Align
import Data.Maybe
import Data.List
import Data.Coerce
import Control.Applicative
import Control.Newtype
import GHC.Integer
import GHC.Integer.Logarithms

cork :: (Alternative f) => Endo (f a) -> f a
cork = (`appEndo` empty)

data Slicing a r =
  forall s. Slicing { next  :: a -> s -> s
                    , split :: s -> Bool
                    , start :: s
                    , done  :: s -> r }

instance Functor (Slicing a) where
  fmap f Slicing{..} = Slicing { done = f . done, ..}

scanSlice :: forall g f t a r. (Foldable t, Alternative f, Alternative g)
          => Slicing a r
          -> t a
          -> (g (r, Endo (f a)), (Maybe r, Endo (f a)))
scanSlice Slicing{..} =
  first cork . second (first getLast) . snd
  . foldl' combine (start, mempty)
  where
    combine (state, (slices, remainder)) a =
      let state'     = next a state
          remainder' = remainder <> (Last (Just (done state')), Endo (pure a <|>)) in
      (state', if split state'
               then (slices <> Endo (pure (first (fromJust . getLast) remainder') <|>), mempty)
               else (slices, remainder'))

allSlices :: (Foldable t, Foldable f, Alternative f)
          => Slicing a r -> t a -> ([(r, f a)], (Maybe r, f a))
allSlices slicing =
  second (second cork)
  . first (fmap (second cork))
  . scanSlice slicing

greatestSlice :: (Foldable t, Foldable f, Alternative f)
              => Slicing a r -> t a -> ((Maybe r, f a), (Maybe r, f a))
greatestSlice slicing =
  first ((getLast *** cork)
         . foldMap (first (Last . Just)))
  . second (second cork)
  . scanSlice @[] slicing

powerOf :: Integral a => a -> a -> Bool
n `powerOf` b | b > 1 && 0 <= n =
  n' == b' ^ logBaseInteger b' n'
    where (n', b') = (toInteger n, toInteger b)
n `powerOf` b | otherwise =
  error $ "Log base must be > 1 and number >= 0"

logBaseInteger :: Integer -> Integer -> Integer
logBaseInteger b n = smallInteger (integerLogBase# b n)

sliceMultiplesOf n =
  Slicing { next  = const succ
          , split = \l -> l `mod` n == 0
          , start = 0
          , done  = id }

sliceAlways = Slicing { next = \_ _ -> ()
                      , split = \_ -> True
                      , start = ()
                      , done = id }

sliceNever = Slicing { next = \_ _ -> ()
                     , split = \_ -> False
                     , start = ()
                     , done = id }

slicePowersOf n =
  Slicing { next  = const succ
          , split = (`powerOf` n)
          , start = 0
          , done  = id }

almostPerfect :: forall t f a. Foldable t => (f a -> f a -> f a) -> (a -> f a) -> t a -> f a
almostPerfect _    _    elems | null elems = error "almostPerfect: empty list"
almostPerfect node leaf elems | otherwise =
  fromJust . ala First foldMap . map singular . iterate squish $ bottom
  where
    ((sizeP, perfect), (sizeR, remainder)) = greatestSlice (slicePowersOf 2) elems

    bottom = rpadZipWith (\a -> maybe (leaf a) (node (leaf a) . leaf)) perfect redistributed

    redistributed = remainder  -- change this for little-endian trees

    squish :: [f a] -> [f a]
    squish = map (\[x, y] -> node x y) . map snd . fst . allSlices (sliceMultiplesOf 2)

singular :: [a] -> Maybe a
singular [a] = Just a
singular  _  = Nothing

data Tree a = (Tree a) :-: (Tree a) | L a deriving Show
