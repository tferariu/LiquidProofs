open import Haskell.Prelude

module Lib where

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = Nat
Address = Nat
TxOutRef = Nat
Deadline = Nat

{-# COMPILE AGDA2HS Deadline #-}


ada : AssetClass
ada = 0

data Map (A B : Set) : Set where
 MkMap : List (A × B) -> Map A B

record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r



eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational


record Has0 (a : Set) : Set where
  field
    emptyVal : a
