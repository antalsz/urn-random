{-# LANGUAGE MagicHash, UnboxedTuples, GeneralizedNewtypeDeriving #-}

module Data.Urn.Internal.AlmostPerfect (almostPerfect, reverseBits, almostPerfect', Tree(..)) where

import Data.List.NonEmpty (NonEmpty(..))
import GHC.Integer.Logarithms
import GHC.Exts
import Data.Bits

--------------------------------------------------------------------------------
-- TODO: make this code efficient
import Control.Monad.State.Strict
import Control.Arrow

newtype Consume n s a =
  Consume { getConsume :: State (n, [s]) a }
  deriving (Functor, Applicative, Monad)

runConsume :: Num n => Consume n s a -> [s] -> a
runConsume action stream = evalState (getConsume action) (0, stream)

index :: Consume n s n
index = Consume $ fst <$> get

consume :: Integral n => Int -> Consume n s [s]
consume n = Consume $ do
  (ix,tokens) <- get
  let (consumed,remaining) = splitAt n ss
  consumed <$ put (ix+1, remaining)

almostPerfect' :: (b -> b -> b) -> (a -> b) -> Word -> NonEmpty a -> b
almostPerfect' node leaf size (e0:|elements0) =
  runConsume (go perfectDepth) (e0:elements0)
  where
    perfectDepth  = wordLog2 size
    remainderSize = size - (1 `shiftL` fromIntegral perfectDepth)

    go 0 = do
      i <- index
      if reverseBits perfectDepth i < remainderSize
        then do [l,r] <- consume 2
                pure $ leaf l `node` leaf r
        else do [x]   <- consume 1
                pure $ leaf x

    go depth = node <$> go (depth - 1)
                    <*> go (depth - 1)

data Tree a = Tree a :*: Tree a | L a deriving Show
--------------------------------------------------------------------------------

-- | Create an "almost perfect" tree from a given list of a specified size.
--   Invariants: specified size must match the actual length of the list,
--   and list must be non-empty.
almostPerfect :: (b -> b -> b) -> (a -> b) -> Word -> NonEmpty a -> b
almostPerfect node leaf size (e0:|elements0) =
  case go perfectDepth 0 (e0:elements0) of (tree, _, _) -> tree
  where
    perfectDepth  = wordLog2 size
    remainderSize = size - (1 `shiftL` fromIntegral perfectDepth)

    go 0 index elements
      | reverseBits perfectDepth index < remainderSize
      , l:r:elements' <- elements
        = (leaf l `node` leaf r, elements', index + 1)

      | x:elements' <- elements
        = (leaf x, elements', index + 1)

      | otherwise
        = error $ "almostPerfect: size mismatch: got input of length " ++
                  show (length (e0:|elements0)) ++
                  ", but expected size " ++ show size

    go depth index elements =
      let (l, elements',  index' ) = go (depth - 1) index  elements
          (r, elements'', index'') = go (depth - 1) index' elements'
      in (l `node` r, elements'', index'')

-- | Returns the number formed by snipping out the first @n@ bits of the input
-- and reversing them
-- TODO: Make this more efficient
reverseBits :: Word -> Word -> Word
reverseBits (W# a) (W# x) = W# (go 0## a x)
  where go r 0## _ = r
        go r n   x =
          go ((r <<.# 1#) `or#` (x `and#` 1##))
             (pred# n)
             (x >>.# 1#)

wordLog2 :: Word -> Word
wordLog2 (W# w) = W# (int2Word# (wordLog2# w))

--------------------------------------------------------------------------------
-- Functions on 'Word#' – used just to make 'almostPerfect' read nicely

(-.#) :: Word# -> Word# -> Word#
m -.# n = case m `subWordC#` n of (# r, _ #) -> r
{-# INLINE (-.#) #-}

-- succ# :: Word# -> Word#
-- succ# x = x `plusWord#` 1##
-- {-# INLINE succ# #-}

pred# :: Word# -> Word#
pred# x = x -.# 1##
{-# INLINE pred# #-}

(<<.#) :: Word# -> Int# -> Word#
(<<.#) = uncheckedShiftL#
{-# INLINE (<<.#) #-}

(>>.#) :: Word# -> Int# -> Word#
(>>.#) = uncheckedShiftRL#
{-# INLINE (>>.#) #-}

-- (<.#) :: Word# -> Word# -> Bool
-- m <.# n = case m `ltWord#` n of
--            0# -> False
--            _  -> True
-- {-# INLINE (<.#) #-}
