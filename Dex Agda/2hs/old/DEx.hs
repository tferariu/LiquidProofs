module DEx where

import Numeric.Natural (Natural)

type Deadline = Natural

data State = State{c1 :: AssetClass, c2 :: AssetClass,
                   cmap1 :: [((Rational, PubKeyHash), Integer)],
                   cmap2 :: [((Rational, PubKeyHash), Integer)]}

data Input = Offer PubKeyHash Int CurrencySymbol TokenName Rational
           | Request PubKeyHash CurrencySymbol TokenName Map
           | Cancel PubKeyHash Int CurrencySymbol TokenName Rational

