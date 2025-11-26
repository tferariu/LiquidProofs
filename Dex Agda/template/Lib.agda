{-# OPTIONS --no-eta-equality #-}

open import Haskell.Prelude

module Lib where

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = Nat
Address = Nat
TxOutRef = Nat

ada : AssetClass
ada = 0

data Map (a b : Set) : Set where
 MkMap : List (a × b) -> Map a b

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


{-# COMPILE AGDA2HS CurrencySymbol #-}
{-# COMPILE AGDA2HS TokenName #-}
{-# COMPILE AGDA2HS PubKeyHash #-}
{-# COMPILE AGDA2HS AssetClass #-}
{-# COMPILE AGDA2HS Address #-}
{-# COMPILE AGDA2HS TxOutRef #-}
{-# COMPILE AGDA2HS ada #-}
{-# COMPILE AGDA2HS Map #-}
{-# COMPILE AGDA2HS Rational #-}
{-# COMPILE AGDA2HS numerator #-}
{-# COMPILE AGDA2HS denominator #-}

