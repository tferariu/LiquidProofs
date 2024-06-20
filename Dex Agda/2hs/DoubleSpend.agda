module DoubleSpend where

open import Haskell.Prelude


Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

PubKeyHash = Integer
Value = Nat
Deadline = Nat

{-# COMPILE AGDA2HS Deadline #-}

Label = List (PubKeyHash × Value)

{-# COMPILE AGDA2HS Label #-}


record ScriptContext : Set where
    field
        inputVal    : Nat
        outputVal   : Nat
        outputLabel : Label
        time        : Deadline
        payTo       : PubKeyHash
        payAmt      : Value
        payInAmt    : Value  
        signature   : PubKeyHash
open ScriptContext public



data Input : Set where
  Open     : PubKeyHash -> Input
  Close    : PubKeyHash -> Input
  Withdraw : PubKeyHash -> Value -> Input
  Deposit  : PubKeyHash -> Value -> Input
  Transfer : PubKeyHash -> PubKeyHash -> Value -> Input

{-# COMPILE AGDA2HS Input #-}


lookup' : PubKeyHash -> Label -> Maybe Value
lookup' pkh [] = Nothing
lookup' pkh ((x , y) ∷ xs) = if (pkh == x)
  then (Just y)
  else (lookup' pkh xs)

insert : PubKeyHash -> Value -> Label -> Label
insert pkh val [] = ((pkh , val) ∷ [])
insert pkh val ((x , y) ∷ xs) = if (pkh == x)
  then ((pkh , val) ∷ xs)
  else ((x , y) ∷ (insert pkh val xs))

{-if (pkh == x)
  then (Just y)
  otherwise (lookup' pkh xs)-}

{-
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
-}

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx

checkMembership : PubKeyHash -> Label -> Bool
checkMembership sig lab = case lookup sig lab of λ where
  Nothing -> False
  (Just _) -> True

checkInputs : Value -> ScriptContext -> Bool
checkInputs v ctx = v == payInAmt ctx

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

agdaValidator : Label -> Input -> ScriptContext -> Bool
agdaValidator lab inp ctx = case inp of λ where

    (Open pkh) -> checkSigned pkh ctx && not (checkMembership pkh lab) &&
                  newLabel ctx == insert pkh 0 lab

    (Close pkh) -> True

    (Withdraw pkh val) -> True

-- checkInputs val ctx && (newLabel ctx) == dat + val

    (Deposit pkh val) -> True

-- checkPayment pkh val ctx && oldValue ctx == ((newValue ctx) + val) && val <= dat && (newLabel ctx) + val == dat

    (Transfer from to val) -> True

{-# COMPILE AGDA2HS agdaValidator #-}

{-

  Open     : PubKeyHash -> Input
  Close    : PubKeyHash -> Input
  Withdraw : PubKeyHash -> Value -> Input
  Deposit  : PubKeyHash -> Value -> Input
  Transfer : PubKeyHash -> PubKeyHash -> Value -> Input
agdaValidator : Value -> Input -> ScriptContext -> Bool
agdaValidator dat red ctx = case red of λ where

    (Add val) -> checkInputs val ctx && (newLabel ctx) == dat + val

    (Pay val pkh) -> checkPayment pkh val ctx && oldValue ctx == ((newValue ctx) + val)
                     && val <= dat && (newLabel ctx) + val == dat
      

{-# COMPILE AGDA2HS agdaValidator #-}
-}

