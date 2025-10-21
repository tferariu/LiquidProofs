open import Haskell.Prelude
open import Lib

module ScriptContext (Label : Set) (Value : Set) where

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
        hasTokenIn    : Bool
        hasTokenOut   : Bool
        time          : Deadline
open ScriptContext public


checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx


newDatum : ScriptContext -> Label
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx


checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1


getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx
