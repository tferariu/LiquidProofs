module MultiSigSC where

open import Haskell.Prelude
--open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)


ScriptPurpose = String

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

Sig = String

{-# COMPILE AGDA2HS Sig #-}

Pkh = String

{-# COMPILE AGDA2HS Pkh #-}

data State : Set where
  Holding : State
  Collecting : Nat -> Pkh -> Nat -> List Sig -> State

{-# COMPILE AGDA2HS State #-}

data Input : Set where
  Propose : Nat -> Pkh -> Nat -> Input
  Add     : Sig -> Input
  Pay     : Input
  Cancel  : Input

{-# COMPILE AGDA2HS Input #-}

Inputs = List (Nat × String)
Outputs = List (Nat × String)
Time = Nat

{-# COMPILE AGDA2HS Time #-}
{-# COMPILE AGDA2HS Inputs #-}
{-# COMPILE AGDA2HS Outputs #-}

agdaValidator : List Sig -> State -> Input -> ScriptContext -> Bool
agdaValidator sigs s i c = True
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
  
