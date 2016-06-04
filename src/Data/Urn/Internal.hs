-- TODO: |delete| is wrong!!!

{-# LANGUAGE GeneralizedNewtypeDeriving, PatternSynonyms #-}

module Data.Urn.Internal where

import Prelude hiding (lookup)
import Data.Bifunctor
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

data Urn a = Urn { size  :: !Size
                 , wtree :: !(WTree a) }
           deriving (Eq, Ord, Show)

blookup :: BTree a -> Weight -> a
blookup (BLeaf a) _ =
  a
blookup (BNode (WTree wl l) (WTree _ r)) i
  | i < wl    = blookup l i
  | otherwise = blookup r (i - wl)

lookup :: Urn a -> Weight -> a
lookup = blookup . btree . wtree

foldWTree :: (Weight -> a -> b)
         -> (Weight -> b -> WTree a -> b)
         -> (Weight -> WTree a -> b -> b)
         -> Size -> WTree a
         -> b
foldWTree fLeaf fLeft fRight = go where
  go _    (WLeaf w a)                      = fLeaf  w a
  go path (WNode w l r) | path `testBit` 0 = fRight w l            (go path' r)
                        | otherwise        = fLeft  w (go path' l) r
                        where path' = path `shiftR` 1
{-# INLINABLE foldWTree #-}

insert :: Weight -> a -> Urn a -> Urn a
insert w' a' (Urn size wt) =
  Urn (size+1) $ foldWTree (\w a -> WNode (w+w') (WLeaf w a) (WLeaf w' a'))
                           (\w   -> WNode (w+w'))
                           (\w   -> WNode (w+w'))
                           size wt

uninsert :: Urn a -> (Weight, a, Maybe (Urn a))
uninsert (Urn size wt) =
  case foldWTree (\w a       -> (w, a, Nothing))
                 (\w ul' r   -> case ul' of
                                  (w', a', Just l') -> (w', a', Just $ WNode (w-w') l' r)
                                  (w', a', Nothing) -> (w', a', Just r))
                 (\w l   ur' -> case ur' of
                                  (w', a', Just r') -> (w', a', Just $ WNode (w-w') l r')
                                  (w', a', Nothing) -> (w', a', Just l))
                 (size-1) wt of
    (w', a', mt) -> (w', a', Urn (size-1) <$> mt)

wupdate :: (Weight -> a -> (Weight, a)) -> Weight -> WTree a -> (Weight, a, Weight, a, WTree a)
wupdate upd = go where
  go _ (WLeaf w a) =
    let (wNew, aNew) = upd w a
    in (w, a, wNew, aNew, WLeaf wNew aNew)
  go i (WNode w l@(WTree wl _) r)
    | i < wl    = case go i l of
                    (wOld, aOld, wNew, aNew, l') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l' r)
    | otherwise = case go (i-wl) r of
                    (wOld, aOld, wNew, aNew, r') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l r')

update :: (Weight -> a -> (Weight, a)) -> Weight -> Urn a -> (Weight, a, Weight, a, Urn a)
update upd i (Urn size wt) =
  case wupdate upd i wt of
    (wOld, aOld, wNew, aNew, wt') -> (wOld, aOld, wNew, aNew, Urn size wt')

wreplace :: Weight -> a -> Weight -> WTree a -> (Weight, a, WTree a)
wreplace wNew aNew = go where
  go _ (WLeaf w a) =
    (w, a, WLeaf wNew aNew)
  go i (WNode w l@(WTree wl _) r)
    | i < wl    = case go i l of
                    (w', a', l') -> (w', a', WNode (w-w'+wNew) l' r)
    | otherwise = case go (i-wl) r of
                    (w', a', r') -> (w', a', WNode (w-w'+wNew) l r')

replace :: Weight -> a -> Weight -> Urn a -> (Weight, a, Urn a)
replace wNew aNew i (Urn size wt) = case wreplace wNew aNew i wt of
                                      (w', a', wt') -> (w', a', Urn size wt')

delete :: Weight -> Urn a -> (Weight, a, Maybe (Urn a))
delete i t = case uninsert t of
               (w', a', Just t')   -> case replace w' a' i t' of
                                        (w'', a'', t'') -> (w'', a'', Just t'')
               res@(_, _, Nothing) -> res

singleton :: Weight -> a -> Urn a
singleton w a = Urn { size = 1, wtree = WLeaf w a }

fromList :: [(Weight,a)] -> Maybe (Urn a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldl' (flip $ uncurry insert) (singleton w t) wts

frequencyT :: Urn (Gen a) -> Gen a
frequencyT (Urn _ (WTree w bt)) = blookup bt =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "frequency' used with empty list") frequencyT . fromList

prop_insert_uninsert :: NonZero Weight -> Char -> NonEmptyList (NonZero Weight, Char) -> Bool
prop_insert_uninsert (NonZero w) x (NonEmpty cs) =
  let Just t = fromList $ map (first getNonZero) cs
  in uninsert (insert w x t) == (w, x, Just t)
