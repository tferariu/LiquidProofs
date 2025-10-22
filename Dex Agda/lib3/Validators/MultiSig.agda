open import Haskell.Prelude
open import Lib
open import SimpleValue

module Validators.MultiSig where

data Info : Set where
  Holding : Info
  Collecting : Value -> PubKeyHash -> Deadline -> List PubKeyHash -> Info

{-# COMPILE AGDA2HS Info #-}

Label = (AssetClass × Info)

{-# COMPILE AGDA2HS Label #-}

open import ScriptContext Label Value

data Input : Set where
  Propose : Value -> PubKeyHash -> Deadline -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input
  Close   : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
        maxWait : Deadline
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

--interesting complication if using "x == pkh -> x :: l'" instead

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}


checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payAdr ctx && v == payVal ctx

expired : Deadline -> ScriptContext -> Bool
expired d ctx = (now ctx) > d

notTooLate : Params -> Deadline -> ScriptContext -> Bool
notTooLate par d ctx = (now ctx) + (maxWait par) >= d

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = hasTokenIn ctx

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = hasTokenOut ctx

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
checkValue addr ctx = hasTokenOut ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx



agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

