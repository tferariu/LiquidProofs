open import Haskell.Prelude
open import Lib

module SimpleValue where


Value = Integer

geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

minValue : Value
minValue = 2

instance
  iZero : Has0 Value
  iZero = record { emptyVal = emptyValue } 
