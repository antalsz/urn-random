{-# LANGUAGE LambdaCase, MagicHash, TypeApplications, GADTs, RankNTypes, ScopedTypeVariables, RecordWildCards, ViewPatterns, BangPatterns #-}

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
import GHC.Exts ( Int(..) )

-- | Given a generalized difference-list over some 'Alternative', collapse it
cork :: (Alternative f) => Endo (f a) -> f a
cork = (`appEndo` empty)

-- | A Slicing is a 'Fold' ala Tekmo's Foldl library, but with a predicate attached too
data Slicing a r =
  forall s. Slicing { next  :: a -> s -> s
                    , split :: s -> Bool
                    , start :: s
                    , done  :: s -> r }

instance Functor (Slicing a) where
  fmap f Slicing{..} = Slicing { done = f . done, ..}

-- | A 'Slicing' describes a strategy for dividing an arbitrary 'Foldable' container into
-- pieces. This implements that functionality, returning a container of all the "slices"
-- (each paired with the value of the fold at the end of that slice), and perhaps a
-- remainder, consisting of a final value of the fold, and the segment of the container
-- which did not get terminated by a slice. Note also that the slices are returned as
-- 'Endo (f a)', which means that they are /difference lists/ on 'f'--this means that
-- concatenating all or some slices resulting from this operation can be done efficiently.
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

-- | A special case of 'scanSlice': return all the slices described by the given 'Slicing',
-- as well as any remainder that may exist, paired with the appropriate out-values of the
-- 'Slicing'.
allSlices :: (Alternative f, Foldable t)
          => Slicing a r -> t a -> ([(r, f a)], (Maybe r, f a))
allSlices slicing =
  second (second cork)
  . first (fmap (second cork))
  . scanSlice slicing

-- | A special case of 'scanSlice': split a container into the longest slice described by
-- the given 'Slicing', and the remainder, pairing each with the possible out-value of the
-- 'Slicing', if any such value exists.
greatestSlice :: (Alternative f, Foldable t)
              => Slicing a r -> t a -> ((Maybe r, f a), (Maybe r, f a))
greatestSlice slicing =
  first ((getLast *** cork)
         . foldMap (first (Last . Just)))
  . second (second cork)
  . scanSlice @[] slicing

-- | Tests whether @n@ is a power of @b@
powerOf :: Integral a => a -> a -> Bool
n `powerOf` b | b > 1 && 0 <= n =
  n' == b' ^ logBaseInteger b' n'
    where (n', b') = (toInteger n, toInteger b)
_ `powerOf` _ | otherwise =
  error $ "Log base must be > 1 and number >= 0"

-- | The integral logarithm of @n@ in base @b@
logBaseInteger :: Integer -> Integer -> Integer
logBaseInteger b n = smallInteger (integerLogBase# b n)

integerLog2 :: Integer -> Integer
integerLog2 = logBaseInteger 2

intLog2 :: Int -> Int
intLog2 (I# n) = I# (integerLog2# (smallInteger n))

-- | Slice every @n@ elements of a container
sliceMultiplesOf :: Integral n => n -> Slicing b n
sliceMultiplesOf n =
  Slicing { next  = const succ
          , split = \l -> l `mod` n == 0
          , start = 0
          , done  = id }

-- | Slice every time the cumulative size of the container so far is a power of @n@
slicePowersOf :: Integral n => n -> Slicing b n
slicePowersOf n =
  Slicing { next  = const succ
          , split = (`powerOf` n)
          , start = 0
          , done  = id }

-- | Build a tree-like structure from the leaves up in a little-endian shape, such that
-- if the structure has exactly a power of 2 number of leaves, it is a perfect shape, but
-- if not, has a one-level-deep fringe. This is linear in time.
almostPerfect :: forall t f n a b. (Foldable t, Integral n, Bits n)
              => (f b -> f b -> f b) -> (a -> f b) -> t a -> (f b, n)
almostPerfect _    _    elems | null elems = error "almostPerfect: empty list"
almostPerfect node leaf elems | otherwise = (tree, sizeTotal)
  where
    tree = fromJust . ala First foldMap . map singular . iterate squish $ bottom

    bottom = rpadZipWith (\a -> maybe (leaf a) (node (leaf a) . leaf) . join) perfect redistributed

    redistributed = stutter (map (< sizeTotal-sizePerfect) positions) remainder

    positions = map (reverseBits (logBaseInteger 2 (fromIntegral sizePerfect))) [0..]

    ((fromMaybe 0           -> sizePerfect, perfect),
     (fromMaybe sizePerfect -> sizeTotal,   remainder)) = greatestSlice (slicePowersOf 2) elems

    squish :: [f b] -> [f b]
    squish = map (\[x, y] -> node x y) . map snd . fst . allSlices (sliceMultiplesOf (2 :: Int))

-- | Return a list of @Maybe a@ such that for each successive @True@ in @bs@, a successive
-- element of @as@ is inserted (but @as@ are not depleted when elements of @bs@ are @False@).
stutter :: [Bool] -> [a] -> [Maybe a]
stutter (True  : bs) (a : as) = Just a  : stutter bs as
stutter (False : bs)      as  = Nothing : stutter bs as
stutter _ [] = []
stutter [] _ = []

-- | Return the head of a list exactly when it is a singleton, and @Nothing@ otherwise
singular :: [a] -> Maybe a
singular [a] = Just a
singular  _  = Nothing

-- | Returns the number formed by snipping out the first @n@ bits of the input and reversing them
-- TODO: Make this more efficient
reverseBits :: (Num n, Eq n, Bits a) => n -> a -> a
reverseBits = go zeroBits
  where go r 0 _ = r
        go r n x =
          go (r `shiftL` 1 .|. bool zeroBits (bit 0) (testBit x 0))
             (n - 1)
             (x `shiftR` 1)

-- | Create an "almost perfect" tree from a given list of a specified size.
--   Invariants: specified size must match the actual length of the list,
--   and list must be non-empty.
unsafeAlmostPerfectFromSize :: (f b -> f b -> f b) -> (a -> f b) -> Int -> [a] -> f b
unsafeAlmostPerfectFromSize _    _    0    = error "unsafeAlmostPerfectFromSize: zero size"
unsafeAlmostPerfectFromSize node leaf size =
  unsafePerfectFromDepth node depthPerfect . perfectBottom
  where
    depthPerfect  = intLog2 size
    sizePerfect   = 1 `shiftL` depthPerfect
    sizeRemainder = size - sizePerfect

    perfectBottom = go 0
      where
        go !n | reverseBits depthPerfect n < sizeRemainder = \case
          (x : y : rest) -> (leaf x `node` leaf y) : go (succ n) rest
          []             -> []
          _              -> error "unsafeAlmostPerfectFromSize: mismatch between stated and actual sizes"
        go !n | otherwise = \case
          (x : rest) -> leaf x : go (succ n) rest
          []         -> []

-- | Create a perfect tree from a power-of-two sized list by combining elements.
--   Invariants: depth must be the floor of the log2 of the length of the list,
--   the list must be non-empty, and the list must be of a length which is some
--   power of two.
unsafePerfectFromDepth :: forall a. (a -> a -> a) -> Int -> [a] -> a
unsafePerfectFromDepth node depth = \case
  [] -> error "unsafePerfectFromDepth: empty list"
  [_] | depth /= 0 -> error "unsafePerfectFromDepth: non-zero depth given for singleton list"
  [a] | otherwise  -> a
  _   | depth <= 0 -> error "unsafePerfectFromDepth: invalid depth (must be log-base-two of list length)"
  as  | otherwise -> fst $ go depth as
  where
    go :: Int -> [a] -> (a, [a])
    go 1 (x : y : rest) = (x `node` y, rest)
    go 1 [_]            = error "unsafePerfectFromDepth: imperfect list (must have a power-of-two length)"
    go d xs = let (!l, xs')  = go (pred d) xs
                  (!r, xs'') = go (pred d) xs'
              in (l `node` r, xs'')

almostPerfect' :: (f b -> f b -> f b) -> (a -> f b) -> [a] -> f b
almostPerfect' node leaf elements =
  unsafeAlmostPerfectFromSize node leaf (length elements) elements

data Tree a = Tree a :*: Tree a | L a deriving Show
