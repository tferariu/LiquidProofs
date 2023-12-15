module MultiSig where

open import Haskell.Prelude
--open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

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

agdaValidator : List Sig -> State -> Input -> Time -> Outputs -> State -> Bool
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
    Cancel -> False
  
