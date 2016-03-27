{-# LANGUAGE GeneralizedNewtypeDeriving, PatternSynonyms #-}
{-# OPTIONS_GHC -funbox-strict-fields -Wall -fno-warn-name-shadowing #-}

module TreeFreq where

import Prelude hiding (lookup)
import Data.Foldable
import Data.Bits
import Test.QuickCheck

type Weight = Word

newtype Size = Size Word deriving ( Eq, Ord, Show, Bounded, Enum
                                  , Num, Real, Integral
                                  , Bits, FiniteBits )

data BTree a = BLeaf a
             | BNode !(WTree a) !(WTree a)
             deriving (Eq, Ord, Show)

data WTree a = WTree { weight :: !Weight
                     , btree  :: !(BTree a) }
             deriving (Eq, Ord, Show)

pattern WLeaf w a   = WTree { weight = w, btree = BLeaf a }
pattern WNode w l r = WTree { weight = w, btree = BNode l r }

data Tree a = Tree { size  :: !Size
                   , wtree :: !(WTree a) }
            deriving (Eq, Ord, Show)

pattern Leaf w a = Tree { size = 1, wtree = WLeaf w a }

blookup :: BTree a -> Weight -> a
blookup (BLeaf a) _ =
  a
blookup (BNode (WTree wl l) (WTree _ r)) i
  | i < wl    = blookup l i
  | otherwise = blookup r (i - wl)

lookup :: Tree a -> Weight -> a
lookup = blookup . btree . wtree

insert :: Weight -> a -> Tree a -> Tree a
insert w' a' (Tree size wt) = Tree (size+1) $ go size wt where
  go _    leaf@(WLeaf w _)                 = WNode (w+w') leaf         (WLeaf w' a')
  go path (WNode w l r) | path `testBit` 0 = WNode (w+w') (go path' l) r
                        | otherwise        = WNode (w+w') l            (go path' r)
                        where path' = path `shiftR` 1

uninsert :: Tree a -> (Weight, a, Maybe (Tree a))
uninsert (Tree size wt) = case go size wt of
                            (w', a', mt) -> (w', a', Tree size <$> mt)
  where
    go _    (WLeaf w a)   = (w, a, Nothing)
    go path (WNode w l r)
      | path `testBit` 0  = case go path' r of
                              (w', a', Just r') -> (w', a', Just $ WNode (w-w') l r')
                              (w', a', Nothing) -> (w', a', Just l)
      | otherwise         = case go path' l of
                              (w', a', Just l') -> (w', a', Just $ WNode (w-w') l' r)
                              (w', a', Nothing) -> (w', a', Just r)
      where path' = path `shiftR` 1

wreplace :: Weight -> a -> Weight -> WTree a -> (Weight, a, WTree a)
wreplace wNew aNew = go where
  go _ (WLeaf w a) =
    (w, a, WLeaf wNew aNew)
  go i (WNode w l@(WTree wl _) r)
    | i < wl    = case go i l of
                    (w', a', l') -> (w', a', WNode (w-w'+wNew) l' r)
    | otherwise = case go (i-wl) r of
                    (w', a', r') -> (w', a', WNode (w-w'+wNew) l r')

replace :: Weight -> a -> Weight -> Tree a -> (Weight, a, Tree a)
replace wNew aNew i (Tree size wt) = case wreplace wNew aNew i wt of
                                       (w', a', wt') -> (w', a', Tree size wt')

delete :: Weight -> Tree a -> (Weight, a, Maybe (Tree a))
delete i t = case uninsert t of
               (w', a', Just t')   -> case replace w' a' i t' of
                                        (w'', a'', t'') -> (w'', a'', Just t'')
               res@(_, _, Nothing) -> res

fromList :: [(Weight,a)] -> Maybe (Tree a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldl' (flip $ uncurry insert) (Leaf w t) wts

frequencyT :: Tree (Gen a) -> Gen a
frequencyT (Tree _ (WTree w bt)) = blookup bt =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "frequency' used with empty list") frequencyT . fromList
