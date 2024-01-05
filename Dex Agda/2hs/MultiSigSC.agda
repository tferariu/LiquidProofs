module MultiSigSC where

open import Haskell.Prelude
--open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)


Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

record TxInfo : Set where
  field
    txInfoInputs                : Placeholder --[V2.TxInInfo]
    txInfoReferenceInputs       : Nat --[V2.TxInInfo]
    txInfoOutputs               : Placeholder --[V2.TxOut]
    txInfoValidRange            : POSIXTimeRange
    txInfoSignatories           : Placeholder --[V2.PubKeyHash]
    txInfoRedeemers             : Nat --Map ScriptPurpose V2.Redeemer
    txInfoData                  : Nat --Map V2.DatumHash V2.Datum
    txInfoId                    : Nat --V2.TxId
open TxInfo public

record ScriptContext : Set where
    field
        scriptContextTxInfo  : TxInfo
        scriptContextPurpose : ScriptPurpose
open ScriptContext public

PubKeyHash = String
Value = Integer
Deadline = Integer

data Datum : Set where
  Holding : Datum
  Collecting : Value -> PubKeyHash -> Deadline -> List PubKeyHash -> Datum

{-# COMPILE AGDA2HS Datum #-}

data Redeemer : Set where
  Propose : Value -> PubKeyHash -> Deadline -> Redeemer
  Add     : PubKeyHash -> Redeemer
  Pay     : Redeemer
  Cancel  : Redeemer

{-# COMPILE AGDA2HS Redeemer #-}

_∈_ : PubKeyHash -> List PubKeyHash -> Bool
_∈_ pkh [] = False
_∈_ pkh (x ∷ l') = (x == pkh) || (pkh ∈ l')

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

count : List PubKeyHash -> Integer
count [] = 0
count (x ∷ l) = 1 + (count l)

{-# COMPILE AGDA2HS _∈_ #-}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS count #-}

postulate
  txSignedBy : TxInfo -> PubKeyHash -> Bool
  checkSigned : PubKeyHash -> Bool
  checkPayment : PubKeyHash -> Value -> TxInfo -> Bool
  expired : Deadline -> TxInfo -> Bool
  oDat : ScriptContext -> Datum
  oldValue : ScriptContext -> Value
--  checkToken : ThreadToken -> ScriptContext -> Bool

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Integer
open Params public


{-# COMPILE AGDA2HS Params #-}

agdaValidator : Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator param dat red ctx = case dat of λ where
  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> checkSigned sig && sig ∈ (authSigs param) && (case (oDat ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && (pkh == pkh' && (d == d' && (sigs' == insert sig sigs ))) )

    Pay -> (count sigs) >= (nr param) && (case (oDat ctx) of λ where
      Holding -> checkPayment pkh v (scriptContextTxInfo ctx)
      (Collecting _ _ _ _) -> False )
      
    Cancel -> case (oDat ctx) of λ where
      Holding -> expired d (scriptContextTxInfo ctx)
      (Collecting _ _ _ _) -> False
  
  Holding -> case red of λ where

    (Propose v pkh d) -> (oldValue ctx >= v) && (case (oDat ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> (v == v' && (pkh == pkh' && (d == d' && (sigs' == [])))) )
    (Add _) -> False
    Pay -> False
    Cancel -> False 

{-# COMPILE AGDA2HS agdaValidator #-}

{-
agdaValidator l s i t o s' = case s of λ where
  (Collecting v pkh d sigs) -> case i of λ where

    (Propose _ _ _) -> False
    (Add sig) -> True --wip
    Pay -> True --wip
    Cancel -> t > d 
  
  Holding -> case i of λ where

    (Propose v pkh d) -> case s' of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs) -> (v == v' && (pkh == pkh' && (d == d' && (sigs == []))))
    (Add _) -> False
    Pay -> False
    Cancel -> False-}
  
