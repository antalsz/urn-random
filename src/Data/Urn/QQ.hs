{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module Data.Urn.QQ where

import Data.Traversable

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Parse

import Data.Urn.Internal

embedWord :: Word -> Exp
embedWord = LitE . IntegerL . toInteger

embedWeight :: Weight -> Exp
embedWeight = embedWord

embedSize :: Size -> Exp
embedSize (Size s) = ConE 'Size `AppE` embedWord s

embedBTree :: BTree Exp -> Exp
embedBTree (BLeaf a)   = ConE 'BLeaf `AppE` a
embedBTree (BNode l r) = ConE 'BNode `AppE` embedWTree l `AppE` embedWTree r
               
embedWTree :: WTree Exp -> Exp
embedWTree wt =
  RecConE 'WTree [ ('weight, embedWeight $ weight wt)
                 , ('btree,  embedBTree  $ btree  wt) ]

embedTree :: Tree Exp -> Exp
embedTree t = RecConE 'Tree [ ('size,  embedSize  $ size  t)
                            , ('wtree, embedWTree $ wtree t) ]

-- We don't handle extensions
parseUrnList :: String -> Either String [(Word, Exp)]
parseUrnList str =
  case parseExp $ "[" ++ str ++ "]" of
    Left  _ ->
      Left "Parse error in urn"
    Right (ListE tups) ->
      for tups $ \case
        TupE [LitE (IntegerL w), e] | toInteger (minBound :: Word) <= w
                                    , w <= toInteger (maxBound :: Word) ->
          Right (fromInteger w :: Word, e)
        TupE [_, _] ->
          Left $ "A weighted pair in this urn lacked a valid literal weight"
        _ ->
          Left $ "This urn contained a non-pair element"
    Right _ ->
      Left "This urn does not contain a list of pairs"

parseUrn :: String -> Either String (Tree Exp)
parseUrn str = (fromList <$> parseUrnList str) >>= \case
                 Just urn -> Right urn
                 Nothing  -> Left  "Empty urn"

urn :: QuasiQuoter
urn = QuasiQuoter { quoteExp  = either fail (pure . embedTree) . parseUrn
                  , quotePat  = unsupported "patterns"
                  , quoteType = unsupported "types"
                  , quoteDec  = unsupported "declarations" }
  where unsupported what =
          fail $ "Urns are only supported in expressions, not " ++ what
