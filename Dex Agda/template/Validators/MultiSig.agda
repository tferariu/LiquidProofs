open import Haskell.Prelude 
open import Lib
open import Value

module Validators.MultiSig where

-- Defining the types of our Plinth Datum, referred to as Label in Agda
data Info : Set where
  Holding : Info
  Collecting : Value -> PubKeyHash -> Integer -> List PubKeyHash -> Info

{-# COMPILE AGDA2HS Info #-}

Label = (AssetClass × Info)

{-# COMPILE AGDA2HS Label #-}

-- The abstract ScriptContext
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
        tokCurrSymbol : CurrencySymbol
        tokenIn       : Bool
        tokenOut      : Bool
        validInterval : Interval

-- Functions equivalent to Plinth ScriptContext functions or provided by our template
--https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-ledger-api/PlutusLedgerApi-V3-Data-Contexts.html#t:ScriptContext

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

ownAssetClass : TokenName -> ScriptContext -> AssetClass
ownAssetClass tn ctx = ((ScriptContext.tokCurrSymbol ctx) , tn)

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

before : POSIXTime -> Interval -> Bool
before record { getPOSIXTime = time } (start , end) = time < start

after : POSIXTime -> Interval -> Bool
after record { getPOSIXTime = time } (start , end) = time > end

validRange : ScriptContext -> Interval
validRange ctx = ScriptContext.validInterval ctx

-- The type of the Plinth Redeemer, referred to as Input in Agda
data Input : Set where
  Propose : Value -> PubKeyHash -> Integer -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input
  Close   : Input

{-# COMPILE AGDA2HS Input #-}

-- The type of the smart contract parameters
record Params : Set where
    no-eta-equality
    pattern
    field
        authSigs  : List PubKeyHash
        nr : Nat
        maxWait : Integer
open Params public

{-# COMPILE AGDA2HS Params #-}

-- Helper functions of the validator
query : PubKeyHash -> List PubKeyHash -> Bool
query pkh [] = False
query pkh (x ∷ l') = (x == pkh) || query pkh l'

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (pkh == x)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}

expired : Integer -> ScriptContext -> Bool
expired d ctx = before (record { getPOSIXTime = d }) (validRange ctx) 

notTooLate : Params -> Integer -> ScriptContext -> Bool
notTooLate par d ctx = before (record { getPOSIXTime = d - (maxWait par) }) (validRange ctx)

{-# COMPILE AGDA2HS expired #-}
{-# COMPILE AGDA2HS notTooLate #-}

-- The Validator
agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param (tok , lab) red ctx = checkTokenIn tok ctx &&
  (case ((checkTokenOut tok ctx) , lab , red) of λ where
    (True , Holding , (Propose v pkh d)) ->
      (newValue ctx == oldValue ctx) && geq (oldValue ctx) v &&
      lovelaces v >= lovelaces minValue && notTooLate param d ctx && continuing ctx &&
      (case (newDatum ctx) of λ where
        (tok' , Holding) -> False
        (tok' , (Collecting v' pkh' d' sigs')) ->
          v == v' && pkh == pkh' && d == d' && sigs' == [] && tok == tok' )
    (True , (Collecting v pkh d sigs) , (Add sig)) ->
      newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) &&
      continuing ctx && (case (newDatum ctx) of λ where
        (tok' , Holding) -> False
        (tok' , (Collecting v' pkh' d' sigs')) ->
          v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs && tok == tok' )
    (True , (Collecting v pkh d sigs) , Pay) ->
      (lengthNat sigs) >= (nr param) && continuing ctx && (case (newDatum ctx) of λ where
        (tok' , Holding) -> 
          checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v) &&
          tok == tok'
        (tok' , (Collecting v' pkh' d' sigs')) -> False)
    (True , (Collecting v pkh d sigs) , Cancel) ->
      newValue ctx == oldValue ctx && continuing ctx &&
      (case (newDatum ctx) of λ where
        (tok' , Holding) -> expired d ctx && tok == tok'
        (tok' , (Collecting v' pkh' d' sigs')) -> False)
    (False , Holding , Close) -> lovelaces 2xMinValue > lovelaces (oldValue ctx) && not (continuing ctx) &&
                                 checkTokenBurned tok ctx
    _ -> False )


{-# COMPILE AGDA2HS agdaValidator #-}

-- Helper functions of the Minting Policy Script
checkDatum : Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx = case (newDatumAddr addr ctx) of λ where
  (tok , Holding) -> ownAssetClass tn ctx == tok
  (tok , (Collecting _ _ _ _)) -> False

checkValue : Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx = lovelaces 2xMinValue < lovelaces (newValueAddr addr ctx) && checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

notIn : PubKeyHash -> List PubKeyHash -> Bool
notIn x [] = True
notIn x (y ∷ ys) = if x == y then False else notIn x ys

noDups : List PubKeyHash -> Bool
noDups [] = True
noDups (x ∷ xs) = notIn x xs && noDups xs

checkParams : Params -> Bool
checkParams record { authSigs = authSigs ; nr = nr ; maxWait = maxWait }
  = (noDups authSigs) && (lengthNat authSigs >= nr) && maxWait > 0 

isInitial : Params -> Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial par addr oref tn ctx = consumes oref ctx &&
                          checkDatum addr tn ctx &&
                          checkValue addr tn ctx &&
                          checkParams par


{-# COMPILE AGDA2HS notIn #-}
{-# COMPILE AGDA2HS noDups #-}
{-# COMPILE AGDA2HS checkParams #-}
{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS isInitial #-}

-- The Thread Token Minting Policy
agdaPolicy : Params -> Address -> TxOutRef -> TokenName -> ⊤ -> ScriptContext -> Bool
agdaPolicy par addr oref tn _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial par addr oref tn ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

