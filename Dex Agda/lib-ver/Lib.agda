module Lib where

open import Haskell.Prelude

CurrencySymbol = Nat
TokenName = Nat
PubKeyHash = Nat 
AssetClass = Nat
Address = Nat
TxOutRef = Nat
Deadline = Nat

{-# COMPILE AGDA2HS Deadline #-}

data Map (A B : Set) : Set where
 MkMap : List (A × B) -> Map A B

Value = Map AssetClass Integer

addValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val + val') ∷ (addValueAux xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValueAux xs v2)
                                       else (ac' , val') ∷ (addValueAux v1 ys))

addValue : Value -> Value -> Value
addValue (MkMap v1) (MkMap v2) = MkMap (addValueAux v1 v2)


subValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
subValueAux [] [] = []
subValueAux [] (v ∷ vs) = v ∷ vs
subValueAux (v ∷ vs) [] = v ∷ vs
subValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val - val') ∷ (addValueAux xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValueAux xs v2)
                                       else (ac' , val') ∷ (addValueAux v1 ys))

subValue : Value -> Value -> Value
subValue (MkMap v1) (MkMap v2) = MkMap (subValueAux v1 v2)

negateValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer)
negateValueAux [] = []
negateValueAux ((fst , Integer.pos zero) ∷ xs) = ((fst , Integer.pos zero) ∷ (negateValueAux xs))
negateValueAux ((fst , Integer.pos (suc n)) ∷ xs) = ((fst , Integer.negsuc n) ∷ (negateValueAux xs))
negateValueAux ((fst , Integer.negsuc n) ∷ xs) = ((fst , Integer.pos (suc n)) ∷ (negateValueAux xs))

negateValue : Value -> Value
negateValue (MkMap x) = MkMap (negateValueAux x)

absValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer)
absValueAux [] = []
absValueAux ((fst , Integer.pos n) ∷ xs) = ((fst , Integer.pos n) ∷ (absValueAux xs))
absValueAux ((fst , Integer.negsuc n) ∷ xs) = ((fst , Integer.pos (suc n)) ∷ (absValueAux xs))

absValue : Value -> Value
absValue (MkMap x) = MkMap (absValueAux x)

signValue : Value -> Value
signValue v = MkMap []

integerToValue : Integer -> Value
integerToValue i = MkMap ( (0 , i) ∷ [])

eqValue : Value -> Value -> Bool
eqValue (MkMap v1) (MkMap v2) = v1 == v2

ltVal : Value -> Value -> Bool
ltVal (MkMap v1) (MkMap v2) = v1 < v2 

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

open import Haskell.Prim.Num

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

  iOrdFromLessThanValue : OrdFromLessThan Value
  iOrdFromLessThanValue .OrdFromLessThan._<_ = ltVal

  iOrdVal : Ord Value
  iOrdVal = record
    { OrdFromLessThan iOrdFromLessThanValue }

  iNumberValue : Number Value
  iNumberValue = record { Constraint = λ x → x ≡ x ; fromNat = λ n → MkMap ((0 , (Integer.pos n)) ∷ []) }
  
  iNumValue : Num Value
  iNumValue .MinusOK _ _         = ⊤
  iNumValue .NegateOK _          = ⊤
  iNumValue .Num.FromIntegerOK _ = ⊤
  iNumValue ._+_ x y             = addValue x y
  iNumValue ._-_ x y             = subValue x y
  iNumValue ._*_ x y             = MkMap []
  iNumValue .negate x            = negateValue x
  iNumValue .abs x               = absValue x
  iNumValue .signum x            = signValue x
  iNumValue .fromInteger n       = integerToValue n



