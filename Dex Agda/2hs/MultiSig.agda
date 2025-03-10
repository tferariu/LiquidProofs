module MultiSig where

open import Haskell.Prelude


Placeholder = Nat
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder

Address = Placeholder
TxOutRef = Placeholder
TokenName = Placeholder

PubKeyHash = Integer
Value = Nat
Deadline = Nat
ThreadToken = Placeholder

{-# COMPILE AGDA2HS Deadline #-}

data Label : Set where
  Holding : Label
  Collecting : Value -> PubKeyHash -> Deadline -> List PubKeyHash -> Label

{-# COMPILE AGDA2HS Label #-}

Datum = (ThreadToken × Label)

{-# COMPILE AGDA2HS Datum #-}

record ScriptContext : Set where
    field
        inputVal    : Nat
        outputVal   : Nat
        outputLabel : Label
        time        : Deadline
        payTo       : PubKeyHash
        payAmt      : Value
        signature   : PubKeyHash
        continues   : Bool
        inputRef    : TxOutRef
        hasTokenIn  : Bool
        hasTokenOut : Bool
        outputAddr  : Address
        mint        : Integer
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

--interesting complication if using "x == pkh -> x :: l'" instead

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

newLabel : ScriptContext -> Label
newLabel ctx = outputLabel ctx

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

agdaValidator : Params -> Datum -> Input -> ScriptContext -> Bool
agdaValidator param (tok , dat) red ctx = case dat of λ where

  Holding -> case red of λ where

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && geq v minValue && notTooLate param d ctx && continuing ctx && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == [] )
    (Add _) -> False
    Pay -> False
    Cancel -> False
    Close -> gt minValue (oldValue ctx) && not (continuing ctx)

  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && continuing ctx && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs )

    Pay -> (lengthNat sigs) >= (nr param) && continuing ctx && (case (newLabel ctx) of λ where
      Holding -> checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v) && checkSigned pkh ctx
      (Collecting _ _ _ _) -> False )
      
    Cancel -> newValue ctx == oldValue ctx && continuing ctx && (case (newLabel ctx) of λ where
      Holding -> expired d ctx
      (Collecting _ _ _ _) -> False)

    Close -> False
  

{-# COMPILE AGDA2HS agdaValidator #-}



getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newLabel ctx) of λ where
  Holding -> True
  (Collecting _ _ _ _) -> False

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
  if      amt == 1  then isInitial addr oref ctx
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

{-
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx
  | amt == 1 =
      hasUTxO
        && checkDatum
        && checkValue
  | amt == -1 = noOutput
  | otherwise = error ()
  where

    hasUTxO :: Bool
    hasUTxO = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs info

    scriptOutput :: TxOut
    scriptOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
      [o] -> o
      _ -> error ()

    checkDatum :: Bool
    checkDatum = case txOutDatum scriptOutput of
      NoOutputDatum -> error ()
      OutputDatumHash dh -> case smDatum $ findDatum dh info of
        Nothing -> error ()
        Just d -> tToken d == AssetClass (cs, tn) && label d == Holding
      OutputDatum dat -> case PlutusTx.unsafeFromBuiltinData @State (getDatum dat) of
        d -> tToken d == AssetClass (cs, tn) && label d == Holding
        _ -> error ()

    checkValue :: Bool
    checkValue = valueOf (txOutValue scriptOutput) cs tn == 1
    
    noOutput :: Bool
    noOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
      [] -> True
      _ -> False

-}
