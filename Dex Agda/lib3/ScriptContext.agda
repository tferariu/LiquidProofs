open import Haskell.Prelude
open import Lib

module ScriptContext (Label : Set) (Value : Set) where

record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payAdr1       : PubKeyHash
        payVal1       : Value
        payAdr2       : PubKeyHash
        payVal2       : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
        tokenIn       : Bool
        tokenOut      : Bool
        time          : Deadline
open ScriptContext

newDatum : ScriptContext -> Label
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

payAdr : ScriptContext -> PubKeyHash
payAdr = payAdr1

payVal : ScriptContext -> Value
payVal = payVal1

buyAdr : ScriptContext -> PubKeyHash
buyAdr = payAdr2

buyVal : ScriptContext -> Value
buyVal = payVal2

sig : ScriptContext -> PubKeyHash
sig = signature

iRef : ScriptContext -> TxOutRef
iRef = inputRef

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

hasTokenIn : ScriptContext -> Bool
hasTokenIn = tokenIn

hasTokenOut : ScriptContext -> Bool
hasTokenOut = tokenOut

now : ScriptContext -> Deadline
now = time

{-
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payAdr1       : PubKeyHash
        payVal1       : Value
        payAdr2       : PubKeyHash
        payVal2       : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
        hasTokenIn    : Bool
        hasTokenOut   : Bool
        time          : Deadline-}
        
checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx


checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx
