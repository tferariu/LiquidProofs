module ScriptContext (Label : Set) where

open import Haskell.Prelude
open import Lib

record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payTo         : PubKeyHash
        payVal        : Value
        buyTo         : PubKeyHash
        buyVal        : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
        time          : Deadline
open ScriptContext public

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx

newDatum : ScriptContext -> Label
newDatum ctx = outputDatum ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

ada : AssetClass
ada = 0

minValue : Value
minValue = MkMap ((ada , 2) ∷ [])


geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = MkMap []


assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (MkMap []) ac = 0
assetClassValueOf (MkMap ((ac' , amt) ∷ vs)) ac = if ac' == ac then amt else assetClassValueOf (MkMap vs) ac


checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 2

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = (assetClassValueOf (inputVal ctx) tok) == 1

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = (assetClassValueOf (outputVal ctx) tok) == 1

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = MkMap ((ac , amt) ∷ [])

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

{-# COMPILE AGDA2HS checkMinValue #-}
{-# COMPILE AGDA2HS checkTokenIn #-}
{-# COMPILE AGDA2HS checkTokenOut #-}
