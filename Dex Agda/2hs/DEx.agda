module DEx where

open import Haskell.Prelude


Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencyScript = Placeholder
TokenName = Placeholder


PubKeyHash = Integer --no longer string because of equality issues
Value = Nat
Deadline = Nat

{-# COMPILE AGDA2HS Deadline #-}

Map = Placeholder

record ScriptContext : Set where
    field
  --      scriptContextTxInfo  : TxInfo
  --      scriptContextPurpose : ScriptPurpose
        inputVal    : Nat
        outputVal   : Nat
  --      outputLabel : Label
        time        : Deadline
        payTo       : PubKeyHash
        payAmt      : Value
        signature   : PubKeyHash
open ScriptContext public

record Rational : Set where
    field
  --      scriptContextTxInfo  : TxInfo
  --      scriptContextPurpose : ScriptPurpose
        num    : Integer
        den    : Integer
open Rational public

record State : Set where
  field
    c1   : CurrencyScript × TokenName
    c2   : CurrencyScript × TokenName
    v    : Value
    omap : Map

data Input : Set where
  Offer   : PubKeyHash -> Value -> CurrencyScript -> TokenName -> Rational -> Input
  Request : PubKeyHash -> CurrencyScript -> TokenName -> Map -> Input
  Cancel  : PubKeyHash -> Value -> CurrencyScript -> TokenName -> Rational -> Input

{-# COMPILE AGDA2HS Input #-}

agdaValidator : State -> Input -> ScriptContext -> Bool
agdaValidator dat red ctx = case red of λ where
  (Offer pkh v cs tn r) -> True
  (Request pkh cs tn map) -> True
  (Cancel pkh v cs tn r) -> True
{-
query : PubKeyHash -> List PubKeyHash -> Bool
query pkh [] = False
query pkh (x ∷ l') = (x == pkh) || query pkh l'

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
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

newLabel : ScriptContext -> Label
newLabel ctx = outputLabel ctx

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

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
open Params public


{-# COMPILE AGDA2HS Params #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx = case dat of λ where

  Holding -> case red of λ where

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && gt v emptyValue && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == [] )
    (Add _) -> False
    Pay -> False
    Cancel -> False 

  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs )

    Pay -> (lengthNat sigs) >= (nr param) && (case (newLabel ctx) of λ where
      Holding -> checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v)
      (Collecting _ _ _ _) -> False )
      
    Cancel -> newValue ctx == oldValue ctx && (case (newLabel ctx) of λ where
      Holding -> expired d ctx
      (Collecting _ _ _ _) -> False)
  

{-# COMPILE AGDA2HS agdaValidator #-}


-}
