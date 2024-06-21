module AccountSim where

open import Haskell.Prelude


Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

PubKeyHash = Integer
Value = Integer

Label = List (PubKeyHash × Value)

{-# COMPILE AGDA2HS Label #-}


record ScriptContext : Set where
    field
        inputVal    : Integer
        outputVal   : Integer
        outputLabel : Label
        payTo       : PubKeyHash
        payAmt      : Value
        signature   : PubKeyHash
open ScriptContext public



data Input : Set where
  Open     : PubKeyHash -> Input
  Close    : PubKeyHash -> Input
  Withdraw : PubKeyHash -> Value -> Input
  Deposit  : PubKeyHash -> Value -> Input
  Transfer : PubKeyHash -> PubKeyHash -> Value -> Input

{-# COMPILE AGDA2HS Input #-}


insert : PubKeyHash -> Value -> Label -> Label
insert pkh val [] = ((pkh , val) ∷ [])
insert pkh val ((x , y) ∷ xs) = if (pkh == x)
  then ((pkh , val) ∷ xs)
  else ((x , y) ∷ (insert pkh val xs))
  
delete : PubKeyHash -> Label -> Label
delete pkh [] = []
delete pkh ((x , y) ∷ xs) = if (pkh == x)
  then xs
  else ((x , y) ∷ (delete pkh xs))

{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS delete #-}

{-if (pkh == x)
  then (Just y)
  otherwise (lookup' pkh xs)-}

{-
lookup' : PubKeyHash -> Label -> Maybe Value
lookup' pkh [] = Nothing
lookup' pkh ((x , y) ∷ xs) = if (pkh == x)
  then (Just y)
  else (lookup' pkh xs)

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

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = pkh == signature ctx

checkMembership : PubKeyHash -> Label -> Bool
checkMembership pkh lab = case lookup pkh lab of λ where
  Nothing -> False
  (Just _) -> True

checkEmpty : PubKeyHash -> Label -> Bool
checkEmpty pkh lab = case lookup pkh lab of λ where
  Nothing -> False
  (Just v) -> v == 0

checkWithdraw : PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkWithdraw pkh val lab ctx = case lookup pkh lab of λ where
  Nothing -> False
  (Just v) -> val >= 0 && v >= val && (newLabel ctx == insert pkh (v - val) lab)
  
checkDeposit : PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkDeposit pkh val lab ctx = case lookup pkh lab of λ where
  Nothing -> False
  (Just v) -> val >= 0 && (newLabel ctx == insert pkh (v + val) lab)

checkTransfer : PubKeyHash -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkTransfer from to val lab ctx = case (lookup from lab , lookup to lab) of λ where
  (Just vF , Just vT) -> vF >= val && val >= 0 && from /= to &&
                         newLabel ctx == insert from (vF - val) (insert to (vT + val) lab)
  _ -> False

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx



agdaValidator : Label -> Input -> ScriptContext -> Bool
agdaValidator lab inp ctx = case inp of λ where

    (Open pkh) -> checkSigned pkh ctx && not (checkMembership pkh lab) &&
                  newLabel ctx == insert pkh 0 lab && newValue ctx == oldValue ctx

    (Close pkh) -> checkSigned pkh ctx && checkEmpty pkh lab &&
                   newLabel ctx == delete pkh lab && newValue ctx == oldValue ctx

    (Withdraw pkh val) -> checkSigned pkh ctx && checkMembership pkh lab &&
                          checkWithdraw pkh val lab ctx && newValue ctx + val == oldValue ctx &&
                          checkPayment pkh val ctx

    (Deposit pkh val) -> checkSigned pkh ctx && checkMembership pkh lab &&
                         checkDeposit pkh val lab ctx && newValue ctx == oldValue ctx + val

    (Transfer from to val) -> checkSigned from ctx && checkMembership from lab &&
                              checkMembership to lab && checkTransfer from to val lab ctx &&
                              newValue ctx == oldValue ctx

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

