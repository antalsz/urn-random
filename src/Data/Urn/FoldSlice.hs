{-# LANGUAGE LambdaCase, MagicHash, ScopedTypeVariables, ViewPatterns, BangPatterns #-}

module Data.Urn.FoldSlice where

import Data.Bool
import Data.Bits
import GHC.Integer
import GHC.Integer.Logarithms
import GHC.Exts ( Int(..) )

intLog2 :: Int -> Int
intLog2 (I# n) = I# (integerLog2# (smallInteger n))

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
unsafeAlmostPerfectFromSize :: (b -> b -> b) -> (a -> b) -> Int -> [a] -> b
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
