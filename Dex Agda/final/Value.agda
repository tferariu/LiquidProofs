open import Lib
open import Haskell.Prelude 

module Value where

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


eqValue : Value -> Value -> Bool
eqValue (MkMap v1) (MkMap v2) = v1 == v2

ltVal : Value -> Value -> Bool
ltVal (MkMap v1) (MkMap v2) = v1 < v2 

emptyValue : Value
emptyValue = MkMap []

minValue : Value
minValue = MkMap ((ada , 2) ∷ [])

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

  iZero : Has0 Value
  iZero = record { emptyVal = emptyValue } 


assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (MkMap []) ac = 0
assetClassValueOf (MkMap ((ac' , amt) ∷ vs)) ac = if ac' == ac then amt else assetClassValueOf (MkMap vs) ac


checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 2
{-# COMPILE AGDA2HS checkMinValue #-}
