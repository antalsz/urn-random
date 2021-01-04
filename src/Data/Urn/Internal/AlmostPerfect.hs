{-# LANGUAGE BangPatterns, MagicHash, UnboxedTuples #-}

module Data.Urn.Internal.AlmostPerfect (almostPerfect, reverseBits#) where

import Data.List.NonEmpty (NonEmpty(..))
import GHC.Integer.Logarithms
import GHC.Exts

-- TODO: Consider moving back to boxed Words, adding a wordLog2 function

-- | Create an "almost perfect" tree from a given list of a specified size.
--   Invariants: specified size must match the actual length of the list,
--   and list must be non-empty.
almostPerfect :: (b -> b -> b) -> (a -> b) -> Word -> NonEmpty a -> b
almostPerfect node leaf (W# size) (e0:|elements0) =
  case go perfectDepth 0## (e0:elements0) of (# tree, _, _ #) -> tree
  where
    perfectDepthInt = wordLog2# size
    perfectDepth    = int2Word# perfectDepthInt
    remainder       = size -.# (1## <<.# perfectDepthInt)

    go 0## index elements
      | reverseBits# perfectDepth index <.# remainder
      , l:r:elements' <- elements
        = (# leaf l `node` leaf r, elements', succ# index #)

      | x:elements' <- elements
        = (# leaf x, elements', succ# index #)

      | otherwise
        = error $ "almostPerfect: size mismatch: got input of length " ++
                  show (length (e0:|elements0)) ++
                  ", but expected size " ++ show (W# size)

    go depth index elements =
      let !(# l, elements',  index'  #) = go (pred# depth) index  elements
          !(# r, elements'', index'' #) = go (pred# depth) index' elements'
      in (# l `node` r, elements'', index'' #)

-- | Returns the number formed by snipping out the first @n@ bits of the input
-- and reversing them
-- TODO: Make this more efficient
reverseBits# :: Word# -> Word# -> Word#
reverseBits# = go 0##
  where go r 0## _ = r
        go r n   x =
          go ((r <<.# 1#) `or#` (x `and#` 1##))
             (pred# n)
             (x >>.# 1#)

--------------------------------------------------------------------------------
-- Functions on 'Word#' – used just to make 'almostPerfect' read nicely

succ# :: Word# -> Word#
succ# x = x `plusWord#` 1##
{-# INLINE succ# #-}

pred# :: Word# -> Word#
pred# x = x -.# 1##
{-# INLINE pred# #-}

(-.#) :: Word# -> Word# -> Word#
(-.#) = minusWord#
{-# INLINE (-.#) #-}

(<<.#) :: Word# -> Int# -> Word#
(<<.#) = uncheckedShiftL#
{-# INLINE (<<.#) #-}

(>>.#) :: Word# -> Int# -> Word#
(>>.#) = uncheckedShiftRL#
{-# INLINE (>>.#) #-}

(<.#) :: Word# -> Word# -> Bool
m <.# n = case m `ltWord#` n of
            0# -> False
            _  -> True
{-# INLINE (<.#) #-}
-- NB: There's an `isTrue#` function, but we may not want to use it; using the
-- direct case generates more efficient core, but if we branch on the result,
-- "the code generator will generate very bad Cmm if [the results of the
-- conditional branch] do allocation."  See Note [Optimizing isTrue#] in
-- "GHC.Types".  And no, we'll never actually be able to see the speed
-- difference, this is purely about doing the Right Thing™ :-)
