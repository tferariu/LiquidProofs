
open import Haskell.Prelude
open import Lib
open import Value

module Validators.MultiSig where

data Info : Set where
  Holding : Info
  Collecting : Value -> PubKeyHash -> Nat -> List PubKeyHash -> Info

{-# COMPILE AGDA2HS Info #-}

Label = (AssetClass × Info)

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

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = getPayment pkh ctx == v

now : ScriptContext -> Nat
now = ScriptContext.time

data Input : Set where
  Propose : Value -> PubKeyHash -> Nat -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input
  Close   : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    no-eta-equality
    field
        authSigs  : List PubKeyHash
        nr : Nat
        maxWait : Nat
open Params public

{-# COMPILE AGDA2HS Params #-}

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


expired : Nat -> ScriptContext -> Bool
expired d ctx = now ctx > d 

notTooLate : Params -> Nat -> ScriptContext -> Bool
notTooLate par d ctx = (now ctx) + (maxWait par) >= d  

{-# COMPILE AGDA2HS expired #-}
{-# COMPILE AGDA2HS notTooLate #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param (tok , lab) red ctx = checkTokenIn tok ctx &&
  (case ((checkTokenOut tok ctx) , lab , red) of λ where
    (True , Holding , (Propose v pkh d)) ->
      (newValue ctx == oldValue ctx) && geq (oldValue ctx) v &&
      geq v minValue && notTooLate param d ctx && continuing ctx &&
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
    (False , Holding , Close) -> gt minValue (oldValue ctx) && not (continuing ctx) &&
                                 checkTokenBurned tok ctx
    _ -> False )


{-# COMPILE AGDA2HS agdaValidator #-}


checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatum ctx) of λ where
  (tok , Holding) -> ownAssetClass ctx == tok
  (tok , (Collecting _ _ _ _)) -> False

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = checkTokenOut (ownAssetClass ctx) ctx

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

