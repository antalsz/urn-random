{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Data.Urn.Internal.AlmostPerfect (almostPerfect, reverseBits#) where

import GHC.Integer.Logarithms
import GHC.Exts

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

-- | Create an "almost perfect" tree from a given list of a specified size.
--   Invariants: specified size must match the actual length of the list,
--   and list must be non-empty.
almostPerfect :: (b -> b -> b) -> (a -> b) -> Word -> [a] -> b
almostPerfect _    _    0         _        = error "magic: zero size"
almostPerfect node leaf (W# size) elements =
  case go perfectDepth 0## elements of (# tree, _, _ #) -> tree
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
        = error "magic: size was a lie"
     
    go depth index elements =
      let (# l, elements',  index'  #) = go (pred# depth) index  elements
          (# r, elements'', index'' #) = go (pred# depth) index' elements'
      in (# l `node` r, elements'', index'' #)

--------------------------------------------------------------------------------
-- Functions on 'Word#' – used just to make 'almostPerfect' read nicely

(-.#) :: Word# -> Word# -> Word#
m -.# n = case m `subWordC#` n of (# r, _ #) -> r
{-# INLINE (-.#) #-}

succ# :: Word# -> Word#
succ# x = x `plusWord#` 1##
{-# INLINE succ# #-}

pred# :: Word# -> Word#
pred# x = x -.# 1##
{-# INLINE pred# #-}

(<<.#) :: Word# -> Int# -> Word#
(<<.#) = uncheckedShiftL#
{-# INLINE (<<.#) #-}

(>>.#) :: Word# -> Int# -> Word#
(>>.#) = uncheckedShiftRL#
{-# INLINE (>>.#) #-}

(<.#) :: Word# -> Word# -> Bool
m <.# n = case m `ltWord#` n of
           0# -> True
           _  -> False
{-# INLINE (<.#) #-}
