{-# LANGUAGE MagicHash, UnboxedTuples, CPP #-}

module Data.Urn.Internal.AlmostPerfect (almostPerfect) where

import Data.List.NonEmpty (NonEmpty(..))
import GHC.Exts
#include "MachDeps.h"

-- TODO: Consider moving back to boxed Words

-- | Create an "almost perfect" tree from a given list of a specified size.
--   Invariants: specified size must match the actual length of the list,
--   and list must be non-empty.
almostPerfect :: (b -> b -> b) -> (a -> b) -> Word -> NonEmpty a -> b
almostPerfect node leaf (W# size) (e0:|elements0) =
  case go perfectDepth 0## (e0:elements0) of (# tree, _ #) -> tree
  where
    perfectDepth = {- ⌊lg size⌋ -}
                   word2Int# ((WORD_SIZE_IN_BITS## -.# 1##) -.# clz# size)

    pathLimit    = {- size - 2^perfectDepth -}
                   (size -.# (1## <<.# perfectDepth))
                     {- … left-shifted to the top of the word -}
                     <<.# (WORD_SIZE_IN_BITS# -# perfectDepth)

    highBit      = {- 0b10…0 -}
                   1## <<.# (WORD_SIZE_IN_BITS# -# 1#)

    go 0# path elements
      | path <.# pathLimit
      , l:r:elements' <- elements
        = (# leaf l `node` leaf r, elements' #)

      | x:elements' <- elements
        = (# leaf x, elements' #)

      | otherwise
        = error $ "almostPerfect: size mismatch: got input of length " ++
                  show (length (e0:|elements0)) ++
                  ", but expected size " ++ show (W# size)

    go depth path elements =
      let path' = path >>.# 1#
          (# l, elements'  #) = go (depth -# 1#) path'                 elements
          (# r, elements'' #) = go (depth -# 1#) (path' `or#` highBit) elements'
      in (# l `node` r, elements'' #)

--------------------------------------------------------------------------------
-- Functions on 'Word#' – used just to make 'almostPerfect' read more nicely

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
