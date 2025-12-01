open import Haskell.Prelude
open import Lib
open import Value

module Validators.DEx where

record Info : Set where
  no-eta-equality
  pattern
  field
    ratio  : Rational
    owner  : PubKeyHash
open Info public

eqInfo : Info -> Info -> Bool
eqInfo b c = (ratio b == ratio c) &&
             (owner b == owner c)

instance
  iEqInfo : Eq Info
  iEqInfo ._==_ = eqInfo


Label = (AssetClass × Info)

{-# COMPILE AGDA2HS Info #-}
{-# COMPILE AGDA2HS Label #-}

record ScriptContext : Set where
    field     
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payments      : List (PubKeyHash × Value)
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
        tokenIn       : Bool
        tokenOut      : Bool
        time          : Nat

newDatum : ScriptContext -> Label
newDatum ctx = ScriptContext.outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = ScriptContext.continues ctx

getPayment' : PubKeyHash -> List (PubKeyHash × Value) -> Value
getPayment' pkh [] = emptyValue
getPayment' pkh ((pkh' , v) ∷ xs) = if pkh == pkh' then v else getPayment' pkh xs

getPayment : PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = getPayment' pkh (ScriptContext.payments ctx)

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = ScriptContext.mint ctx 

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = ScriptContext.tokAssetClass ctx

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn ac = ScriptContext.tokenIn

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut ac = ScriptContext.tokenOut
        
checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == ScriptContext.signature ctx

sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = ScriptContext.mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == ScriptContext.inputRef ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = ScriptContext.continues ctx

newDatumAddr : Address -> ScriptContext -> Label
newDatumAddr adr ctx = newDatum ctx

newValueAddr : Address -> ScriptContext -> Value
newValueAddr adr ctx = newValue ctx

checkTokenOutAddr : Address -> AssetClass -> ScriptContext -> Bool
checkTokenOutAddr adr = checkTokenOut

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = getPayment pkh ctx == v

now : ScriptContext -> Nat
now = ScriptContext.time


data Input : Set where
  Update   : Value -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    no-eta-equality
    pattern
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}


checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (numerator r) <= b * (denominator r)

checkPaymentRatio : PubKeyHash -> Integer -> AssetClass -> Rational -> ScriptContext -> Bool
checkPaymentRatio pkh amt ac r ctx = ratioCompare amt (assetClassValueOf (getPayment pkh ctx) ac) r && checkMinValue (getPayment pkh ctx)


{-# COMPILE AGDA2HS checkRational #-}
{-# COMPILE AGDA2HS ratioCompare #-}
{-# COMPILE AGDA2HS checkPaymentRatio #-}


agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par (tok , lab) red ctx = checkTokenIn tok ctx && (case red of λ where
  (Update v r) -> checkSigned (owner lab) ctx &&
                    checkRational r && checkMinValue v &&
                    newValue ctx == v &&
                    newDatum ctx == (tok , record {ratio = r ; owner = owner lab}) &&
                    continuing ctx && checkTokenOut tok ctx
  (Exchange amt pkh) -> oldValue ctx == newValue ctx + (assetClassValue (sellC par) amt) &&
                        newDatum ctx == (tok , lab) &&
                        checkPaymentRatio (owner lab) amt (buyC par) (ratio lab) ctx && 
                        continuing ctx && checkTokenOut tok ctx
  Close -> not (continuing ctx) && checkTokenBurned tok ctx &&
           not (checkTokenOut (newDatum ctx .fst) ctx) && checkSigned (owner lab) ctx )
           
{-# COMPILE AGDA2HS agdaValidator #-}

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatumAddr addr ctx) of λ where
  (tok , l) -> ownAssetClass ctx == tok && checkRational (ratio l)

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = checkTokenOutAddr addr (ownAssetClass ctx) ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx


{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS isInitial #-}

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx


{-# COMPILE AGDA2HS agdaPolicy #-}




