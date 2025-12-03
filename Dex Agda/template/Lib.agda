open import Haskell.Prelude

module Lib where

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = (TokenName × CurrencySymbol)
Address = Nat
TxOutRef = Nat

ada : AssetClass
ada = (0 , 0)

data Map (a b : Set) : Set where
 MkMap : List (a × b) -> Map a b

record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = Rational.num r

denominator : Rational -> Integer
denominator r = Rational.den r



eqRational : Rational -> Rational -> Bool
eqRational b c = (numerator b == numerator c) &&
                 (denominator b == denominator c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = numerator b * denominator c < numerator c * denominator b


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational
