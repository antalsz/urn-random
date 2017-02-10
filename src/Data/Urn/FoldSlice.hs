{-# LANGUAGE LambdaCase, MagicHash, TypeApplications, GADTs, RankNTypes, ScopedTypeVariables, RecordWildCards, ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

module Data.Urn.FoldSlice where

import Data.Monoid
import Data.Foldable
import Data.Bool
import Data.Bits
import Control.Arrow
import Data.Align
import Data.Maybe
import Control.Applicative
import Control.Monad
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

allSlices :: (Alternative f, Foldable t)
          => Slicing a r -> t a -> ([(r, f a)], (Maybe r, f a))
allSlices slicing =
  second (second cork)
  . first (fmap (second cork))
  . scanSlice slicing

greatestSlice :: (Alternative f, Foldable t)
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
_ `powerOf` _ | otherwise =
  error $ "Log base must be > 1 and number >= 0"

logBaseInteger :: Integer -> Integer -> Integer
logBaseInteger b n = smallInteger (integerLogBase# b n)

sliceMultiplesOf :: Integer -> Slicing b Integer
sliceMultiplesOf n =
  Slicing { next  = const succ
          , split = \l -> l `mod` n == 0
          , start = 0
          , done  = id }

slicePowersOf :: Integer -> Slicing b Integer
slicePowersOf n =
  Slicing { next  = const succ
          , split = (`powerOf` n)
          , start = 0
          , done  = id }

almostPerfect :: forall t f a b. Foldable t => (f b -> f b -> f b) -> (a -> f b) -> t a -> f b
almostPerfect _    _    elems | null elems = error "almostPerfect: empty list"
almostPerfect node leaf elems | otherwise =
  fromJust . ala First foldMap . map singular . iterate squish $ bottom
  where
    ((                       fromMaybe 0 -> sizePerfect  , perfect),
     (subtract sizePerfect . fromMaybe 0 -> sizeRemainder, remainder)) =
      greatestSlice (slicePowersOf 2) elems

    bottom = rpadZipWith (\a -> maybe (leaf a) (node (leaf a) . leaf) . join) perfect redistributed

    -- redistributed = map Just remainder  -- change this for little-endian trees
    redistributed = stutter positions remainder
    positions = map ((< sizeRemainder) . reverseBits (logBaseInteger 2 sizePerfect)) [0..]

    squish :: [f b] -> [f b]
    squish = map (\[x, y] -> node x y) . map snd . fst . allSlices (sliceMultiplesOf 2)

singular :: [a] -> Maybe a
singular [a] = Just a
singular  _  = Nothing

stutter :: [Bool] -> [a] -> [Maybe a]
stutter (True  : bs) (a : as) = Just a  : stutter bs      as
stutter (False : bs) (a : as) = Nothing : stutter bs (a : as)
stutter _ [] = []
stutter [] _ = undefined

reverseBits :: (Num n, Eq n, Bits a) => n -> a -> a
reverseBits = go zeroBits
  where go r 0 _ = r
        go r n x =
          go (r `shiftL` 1 .|. bool zeroBits (bit 0) (testBit x 0))
             (n - 1)
             (x `shiftR` 1)

data Tree a = (Tree a) :-: (Tree a) | L a deriving Show
