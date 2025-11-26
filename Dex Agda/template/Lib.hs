module Lib where

import Numeric.Natural (Natural)

type CurrencySymbol = Natural

type TokenName = Natural

type PubKeyHash = Natural

type AssetClass = Natural

type Address = Natural

type TxOutRef = Natural

ada :: AssetClass
ada = 0

data Map a b = MkMap [(a, b)]

data Rational = Rational{num :: Integer, den :: Integer}

numerator :: Rational -> Integer
numerator r = num r

denominator :: Rational -> Integer
denominator r = den r

