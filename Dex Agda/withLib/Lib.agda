open import Haskell.Prelude

module Lib (Datum : Set) (PubKeyHash : Set) (Value : Set) {{EqPkh : Eq PubKeyHash}} {{EqVal : Eq Value}} {{SemiValue : Semigroup Value}} {{OrdFromLessThanValue : OrdFromLessThan Value}} {{iOrdVal : Ord Value}} where

{-
Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Nat
TokenName = Nat 

AssetClass = Nat

Address = Nat
TxOutRef = Nat

data Map (A B : Set) : Set where
 MkMap : List (A × B) -> Map A B

Value = Map AssetClass Integer


addValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val + val') ∷ (addValueAux xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValueAux xs v2)
                                       else (ac' , val') ∷ (addValueAux v1 ys))

addValue : Value -> Value -> Value
addValue (MkMap v1) (MkMap v2) = MkMap (addValueAux v1 v2)

eqValue : Value -> Value -> Bool
eqValue (MkMap v1) (MkMap v2) = v1 == v2

ltVal : Value -> Value -> Bool
ltVal (MkMap v1) (MkMap v2) = v1 < v2 

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

  iOrdFromLessThanValue : OrdFromLessThan Value
  iOrdFromLessThanValue .OrdFromLessThan._<_ = ltVal

  iOrdVal : Ord Value
  iOrdVal = record
    { OrdFromLessThan iOrdFromLessThanValue }



record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Datum
        payTo         : PubKeyHash
        payVal        : Value
        buyTo         : PubKeyHash
        buyVal        : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
open ScriptContext public




checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx

newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

ada : AssetClass
ada = 0

minValue : Value
minValue = MkMap ((ada , 2) ∷ [])

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

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1
-}
{-
Placeholder = Nat
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder

Address = Placeholder
TxOutRef = Placeholder
TokenName = Placeholder

PubKeyHash = Integer
Value = Nat
Deadline = Nat
AssetClass = Nat

{-# COMPILE AGDA2HS Deadline #-}

data Label : Set where
  Holding : Label
  Collecting : Value -> PubKeyHash -> Deadline -> List PubKeyHash -> Label

{-# COMPILE AGDA2HS Label #-}

Datum = (AssetClass × Label)

{-# COMPILE AGDA2HS Datum #-}

record ScriptContext : Set where
    field
        inputVal      : Nat
        outputVal     : Nat
        outputDatum   : Datum
        time          : Deadline
        payTo         : PubKeyHash
        payAmt        : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        hasTokenIn    : Bool
        hasTokenOut   : Bool
        mint          : Integer
        tokAssetClass : AssetClass
open ScriptContext public


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

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx

expired : Deadline -> ScriptContext -> Bool
expired d ctx = (time ctx) > d

notTooLate : Params -> Deadline -> ScriptContext -> Bool
notTooLate par d ctx = (time ctx) + (maxWait par) >= d

newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

minValue : Value
minValue = 2

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = hasTokenIn ctx

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = hasTokenOut ctx

agdaValidator : Params -> Datum -> Input -> ScriptContext -> Bool
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
    (False , Holding , Close) -> gt minValue (oldValue ctx) && not (continuing ctx)
    _ -> False )


{-# COMPILE AGDA2HS agdaValidator #-}



getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

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

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

-}
