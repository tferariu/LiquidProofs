open import Haskell.Prelude
open import Lib


record ScriptContext : Set where
    field     
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payAdr1       : PubKeyHash
        payVal1       : Value
        payAdr2       : PubKeyHash
        payVal2       : Value
        payments      : List (PubKeyHash × Value)
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
        tokenIn       : Bool
        tokenOut      : Bool
        time          : Deadline

newDatum : ScriptContext -> Label
newDatum ctx = ScriptContext.outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = ScriptContext.continues ctx

{-
payAdr : ScriptContext -> PubKeyHash
payAdr = ScriptContext.payAdr1

payVal : ScriptContext -> Value
payVal = ScriptContext.payVal1

buyAdr : ScriptContext -> PubKeyHash
buyAdr = ScriptContext.payAdr2

buyVal : ScriptContext -> Value
buyVal = ScriptContext.payVal2
-}

getPayment : Nat -> List (PubKeyHash × Value) -> (PubKeyHash × Value)
getPayment zero [] = 0 , Has0.emptyVal iZero
getPayment zero ((fst , snd) ∷ l) = (fst , snd)
getPayment (suc a) [] = 0 , Has0.emptyVal iZero
getPayment (suc a) (x ∷ xs) = getPayment a xs

payAdr : ScriptContext -> PubKeyHash
payAdr ctx = fst (getPayment 0 (ctx .ScriptContext.payments))

payVal : ScriptContext -> Value
payVal ctx = snd (getPayment 0 (ctx .ScriptContext.payments))

buyAdr : ScriptContext -> PubKeyHash
buyAdr ctx = fst (getPayment 1 (ctx .ScriptContext.payments))

buyVal : ScriptContext -> Value
buyVal ctx = snd (getPayment 1 (ctx .ScriptContext.payments))

sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = ScriptContext.mint ctx 

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = ScriptContext.tokAssetClass ctx

hasTokenIn : ScriptContext -> Bool
hasTokenIn = ScriptContext.tokenIn

hasTokenOut : ScriptContext -> Bool
hasTokenOut = ScriptContext.tokenOut

now : ScriptContext -> Deadline
now = ScriptContext.time

        
checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == ScriptContext.signature ctx


checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = ScriptContext.mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == ScriptContext.inputRef ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = ScriptContext.continues ctx
