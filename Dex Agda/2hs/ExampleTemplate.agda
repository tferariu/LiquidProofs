open import Haskell.Prelude

module ExampleTemplate where

PubKeyHash = Integer
AssetClass = Nat
Value = List (AssetClass × Integer)

data Datum : Set where
  Holding : Datum
  Collecting : Value -> PubKeyHash -> Integer -> List PubKeyHash -> Datum

{-# COMPILE AGDA2HS Datum #-}

data Input : Set where
  Propose : Value -> PubKeyHash -> Integer -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input
  Close   : Input

{-# COMPILE AGDA2HS Input #-}

record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Datum

newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx

oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx

validator : Datum -> Input -> ScriptContext -> Bool
validator d i ctx = newValue ctx == oldValue ctx

{-# COMPILE AGDA2HS validator #-}
