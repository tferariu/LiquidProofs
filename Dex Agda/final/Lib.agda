open import Haskell.Prelude

module Lib where

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = Nat
Address = Nat
TxOutRef = Nat
Deadline = Nat

data AssetClass' : Set where
  Ada : AssetClass'
  T1  : AssetClass'
  T2  : AssetClass'
  T3  : AssetClass'
  T4  : AssetClass'
  T5  : AssetClass'

eqAC : AssetClass' -> AssetClass' -> Bool
eqAC Ada Ada = True
eqAC Ada b = False
eqAC T1 T1 = True
eqAC T1 b = False
eqAC T2 T2 = True
eqAC T2 b = False
eqAC T3 T3 = True
eqAC T3 b = False
eqAC T4 T4 = True
eqAC T4 b = False
eqAC T5 T5 = True
eqAC T5 b = False

instance
  iEqAC : Eq AssetClass'
  iEqAC ._==_ = eqAC

{-# COMPILE AGDA2HS PubKeyHash #-}
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
