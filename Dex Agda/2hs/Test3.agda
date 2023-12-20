module Test3 where

open import Haskell.Prelude


ScriptPurpose = String

Placeholder = String

PubKeyHash = String

{-# COMPILE AGDA2HS PubKeyHash #-}

record TxInfo : Set where
  field
    otherStuff        : Placeholder
    txInfoSignatories : List PubKeyHash
    moreOtherStuff    : Placeholder
open TxInfo public

record ScriptContext : Set where
    field
        scriptContextTxInfo  : TxInfo
        scriptContextPurpose : ScriptPurpose
open ScriptContext public

data Datum : Set where
  Holding : Datum
  Collecting : Integer -> PubKeyHash -> Integer -> List PubKeyHash -> Datum

{-# COMPILE AGDA2HS Datum #-}

data Redeemer : Set where
  Propose : Integer -> PubKeyHash -> Integer -> Redeemer
  Add     : PubKeyHash -> Redeemer
  Pay     : Redeemer
  Cancel  : Redeemer

{-# COMPILE AGDA2HS Redeemer #-}

_∈_ : PubKeyHash -> List PubKeyHash -> Bool
_∈_ pkh [] = False
_∈_ pkh (x ∷ l') = (x == pkh) || (pkh ∈ l')

{-# COMPILE AGDA2HS _∈_ #-}

State = Placeholder
Inputs = Placeholder
Outputs = Placeholder
OtherStuff = Placeholder

Transition = Redeemer

agdaValidator : State -> Transition -> State -> Inputs -> Outputs
              -> List PubKeyHash -> OtherStuff -> Bool
agdaValidator s t s' i o sigs stuff = case t of λ where
    (Add pkh) -> pkh ∈ sigs
    _ -> False

{-# COMPILE AGDA2HS agdaValidator #-}

{-


Outputs = List (Nat × String)

{-# COMPILE AGDA2HS Outputs #-}

_∈_ : PubKeyHash -> List PubKeyHash -> Bool
_∈_ pkh [] = False
_∈_ pkh (x ∷ l') = (x == pkh) || (pkh ∈ l')

{-_∈_ pkh l = case l of λ where
  [] -> False
  (x ∷ l') → (x == pkh) || (pkh ∈ l')
-}

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

{-# COMPILE AGDA2HS _∈_ #-}
{-# COMPILE AGDA2HS insert #-}

postulate
  checkSigned : PubKeyHash -> Bool
  checkPayment : PubKeyHash -> Integer -> Outputs -> Bool


agdaValidator : List PubKeyHash -> State -> Input -> Interval -> Outputs -> State -> Bool
agdaValidator l s i t o s' = case s of λ where
  (Collecting v pkh d sigs) -> case i of λ where

    (Propose _ _ _) -> False

    (Add sig) -> case s' of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> checkSigned sig && sig ∈ l && (v == v' && (pkh == pkh' && (d == d' && (sigs' == insert sig sigs ))))

    Pay -> case s' of λ where
      Holding -> checkPayment pkh v o
      (Collecting _ _ _ _) -> False
      
    Cancel -> case s' of λ where
      Holding -> before d t
      (Collecting _ _ _ _) -> False
  
  Holding -> case i of λ where

    (Propose v pkh d) -> case s' of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> (v == v' && (pkh == pkh' && (d == d' && (sigs' == []))))
    (Add _) -> False
    Pay -> False
    Cancel -> False

{-# COMPILE AGDA2HS agdaValidator #-}
  
-}
