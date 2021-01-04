{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module Data.Urn.QQ (urn) where

import Language.Haskell.TH.Quote
import Data.Urn.QQ.ParseExp

urn :: QuasiQuoter
urn = QuasiQuoter { quoteExp  = either fail (pure . urnExp) . parseUrn
                  , quotePat  = unsupported "patterns"
                  , quoteType = unsupported "types"
                  , quoteDec  = unsupported "declarations" }
  where unsupported what _ =
          fail $ "Literal urns are only supported in expressions, not " ++ what
