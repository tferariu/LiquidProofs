open import Haskell.Prelude

module Lib where

--Defining types that already exist in Plinth or are necessary for the abstract implementation of Value

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = (TokenName × CurrencySymbol)
Address = Nat
TxOutRef = Nat
Interval = (Integer × Integer)

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

record POSIXTime : Set where
    no-eta-equality
    pattern
    field
        getPOSIXTime : Integer
open POSIXTime public
