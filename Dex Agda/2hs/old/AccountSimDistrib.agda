module AccountSimDistrib where

open import Haskell.Prelude

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

Address = Nat

PubKeyHash = Integer
Value = Integer
TxOutRef = Nat
AssetClass = Nat


Datum = (AssetClass × PubKeyHash)

{-# COMPILE AGDA2HS Datum #-}


data Input : Set where
  Close       : Input
  Withdraw    : Value -> Input
  Deposit     : Value -> Input
  TransferOut : PubKeyHash -> Value -> Input
  TransferIn  : PubKeyHash -> Value -> Input

{-# COMPILE AGDA2HS Input #-}

record ScriptContext : Set where
    field
        inputVal      : Integer
        outputVal     : Integer
        outputDatum   : Datum
        signature     : PubKeyHash
        otherInputRed : Input
        otherInputDat : Datum
        continues     : Bool
        inputRef      : TxOutRef
        hasTokenIn    : Bool
        hasTokenOut   : Bool
        mint          : Integer
        tokAssetClass : AssetClass
open ScriptContext public





newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

newToken : ScriptContext -> AssetClass
newToken ctx = fst (outputDatum ctx)

newLabel : ScriptContext -> PubKeyHash
newLabel ctx = snd (outputDatum ctx)

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

minValue : Value
minValue = 2

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = pkh == signature ctx

checkOtherInputO : PubKeyHash -> ScriptContext -> Bool
checkOtherInputO pkh ctx = case otherInputRed ctx of λ where
    Close -> False
    (Withdraw val) -> False
    (Deposit val) -> False
    (TransferOut to val) -> False
    (TransferIn from val) -> snd (otherInputDat ctx) == pkh
    
checkOtherInputI : PubKeyHash -> ScriptContext -> Bool
checkOtherInputI pkh ctx = case otherInputRed ctx of λ where
    Close -> False
    (Withdraw val) -> False
    (Deposit val) -> False
    (TransferOut to val) -> to == pkh
    (TransferIn from val) -> False 



checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = hasTokenIn ctx

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = hasTokenOut ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

agdaValidator : Datum -> Input -> ScriptContext -> Bool
agdaValidator (tok , pkh) inp ctx = checkTokenIn tok ctx && (case inp of λ where

    Close -> checkSigned pkh ctx && oldValue ctx == emptyValue && not (continuing ctx)
    
    (Withdraw val) -> checkSigned pkh ctx && geq val emptyValue && geq (oldValue ctx) val &&
                      newValue ctx == oldValue ctx - val &&
                      checkTokenOut tok ctx && continuing ctx && newDatum ctx == (tok , pkh)

    (Deposit val) -> checkSigned pkh ctx && geq val emptyValue && newValue ctx == oldValue ctx + val &&
                     checkTokenOut tok ctx && continuing ctx && newDatum ctx == (tok , pkh)

    (TransferOut to val) -> checkSigned pkh ctx && geq val emptyValue && geq (oldValue ctx) val &&
                         newValue ctx == oldValue ctx - val &&
                         checkTokenOut tok ctx && continuing ctx && newDatum ctx == (tok , pkh) &&
                         checkOtherInputO to ctx 
                
    (TransferIn from val) -> newValue ctx == oldValue ctx + val && geq val emptyValue && 
                        checkTokenOut tok ctx && continuing ctx && newDatum ctx == (tok , pkh) &&
                        checkOtherInputI from ctx )

{-# COMPILE AGDA2HS agdaValidator #-}

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx


checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatum ctx) of λ where
  (tok , map) -> ownAssetClass ctx == tok

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = hasTokenOut ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx

{-# COMPILE AGDA2HS consumes #-}
{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS isInitial #-}
{-# COMPILE AGDA2HS continuingAddr #-}
{-# COMPILE AGDA2HS getMintedAmount #-}

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}


