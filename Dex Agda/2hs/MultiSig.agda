module MultiSig where

open import Haskell.Prelude
--open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)


ScriptPurpose = String

Interval = Bool

before : Integer -> Interval -> Bool
before a b = b

record TxInfo : Set where
  field
    txInfoInputs                : Nat --[V2.TxInInfo]
    txInfoReferenceInputs       : Nat --[V2.TxInInfo]
    txInfoOutputs               : Nat --[V2.TxOut]
    txInfoFee                   : Nat --V2.Lovelace
    txInfoMint                  : Nat --V2.Value
    txInfoTxCerts               : Nat --[TxCert]
    txInfoWdrl                  : Nat --Map V2.Credential V2.Lovelace
    txInfoValidRange            : Nat --V2.POSIXTimeRange
    txInfoSignatories           : Nat --[V2.PubKeyHash]
    txInfoRedeemers             : Nat --Map ScriptPurpose V2.Redeemer
    txInfoData                  : Nat --Map V2.DatumHash V2.Datum
    txInfoId                    : Nat --V2.TxId

record ScriptContext : Set where
    field
        scriptContextTxInfo  : TxInfo
        scriptContextPurpose : ScriptPurpose
open ScriptContext public

PubKeyHash = String

{-# COMPILE AGDA2HS PubKeyHash #-}

data State : Set where
  Holding : State
  Collecting : Integer -> PubKeyHash -> Integer -> List PubKeyHash -> State

{-# COMPILE AGDA2HS State #-}

data Input : Set where
  Propose : Integer -> PubKeyHash -> Integer -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input

{-# COMPILE AGDA2HS Input #-}

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
  
