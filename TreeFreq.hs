{-# LANGUAGE PatternSynonyms, DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

import Prelude hiding (lookup)
import Test.QuickCheck

type Weight = Int

data Tree' a = Leaf' a
             | Node' !(Tree a) !(Tree a)
             deriving (Eq, Ord, Show, Read)

data Tree a = Tree { weight :: !Weight
                   , tree'  :: !(Tree' a) }
            deriving (Eq, Ord, Show, Read)

pattern Leaf w a   = Tree { weight = w, tree' = Leaf' a }
pattern Node w l r = Tree { weight = w, tree' = Node' l r }

-- Precondition: @0 <= i < weight t@
lookup :: Tree' a -> Weight -> a
lookup (Leaf' a)                      _ = a
lookup (Node' (Tree wl l) (Tree _ r)) i
  | i < wl    = lookup l i
  | otherwise = lookup r (i - wl)

insert :: Weight -> a -> Tree a -> Tree a
insert w' a' t@(Leaf w a) = Node (w+w') t (Leaf w' a')
insert w' a' (Node w l r) = Node (w+w') l $ insert w' a' r

delete :: Weight -> Tree a -> (Weight, a, Maybe (Tree a))
delete _ (Leaf w a) =
  (w, a, Nothing)
delete i (Node w l@(Tree wl _) r)
  | i < wl    = case delete i l of
                  (w', a, Just l') -> (w', a, Just $ Node (w-w') l' r)
                  (w', a, Nothing) -> (w', a, Just r)
  | otherwise = case delete (i-wl) r of
                  (w', a, Just r') -> (w', a, Just $ Node (w-w') l r')
                  (w', a, Nothing) -> (w', a, Just l)

fromList :: [(Weight,a)] -> Maybe (Tree a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldr (uncurry insert) (Leaf w t) wts

frequencyT :: Tree (Gen a) -> Gen a
frequencyT (Tree w t) = lookup t =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "URK") frequencyT . fromList

