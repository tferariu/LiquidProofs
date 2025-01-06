module DExpanded where

open import Haskell.Prelude

variable
  k v : Set

Placeholder = String
POSIXTimeRange = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Nat
TokenName = Nat

PubKeyHash = Nat 
Address = Nat

Value = Integer


AssetClass = Nat



record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r

checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

Cmap = List ((Rational × PubKeyHash) × Integer)

record Label : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
open Label public
{-# COMPILE AGDA2HS Label #-}

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

  iOrdRational : Ord Rational
  iOrdRational = ordFromLessThan ltRational


eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel


data OutputDatum : Set where

  Payment : Address -> OutputDatum
  Script : Label -> OutputDatum

eqDatum : OutputDatum -> OutputDatum -> Bool
eqDatum (Payment x) (Payment y) = x == y
eqDatum (Payment x) (Script y) = False
eqDatum (Script x) (Payment y) = False
eqDatum (Script x) (Script y) = x == y

instance
  iEqDatum : Eq OutputDatum
  iEqDatum ._==_ = eqDatum

data ScriptPurpose : Set where

  Spending : Address -> ScriptPurpose
  Minting : CurrencySymbol -> ScriptPurpose

record TxOut : Set where
  field
    txOutAddress : Address
    txOutValue : Value
    txOutDatum : OutputDatum

open TxOut public


record ScriptContext : Set where
    field
        txOutputs   : List TxOut
        inputVal    : Value
        signature   : PubKeyHash
        purpose     : ScriptPurpose
        
        
open ScriptContext public


checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx


data Input : Set where
  Update   : Integer -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}

getContinuingOutput : ScriptContext -> Maybe TxOut
getContinuingOutput record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) } = Nothing
getContinuingOutput record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) } = if adr == txOutAddress txO then Just txO else getContinuingOutput (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending adr })
getContinuingOutput record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) } = Nothing


oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newLabel : ScriptContext -> Maybe Label
newLabel ctx = case getContinuingOutput ctx of λ where
  Nothing -> Nothing
  (Just txO) -> case txOutDatum txO of λ where
    (Payment adr) -> Nothing
    (Script lab) -> Just lab

newValue : ScriptContext -> Maybe Value
newValue ctx = case getContinuingOutput ctx of λ where
  Nothing -> Nothing
  (Just txO) -> Just (txOutValue txO)

continuing : ScriptContext -> Bool
continuing ctx = case getContinuingOutput ctx of λ where
  Nothing -> False
  (Just txO) -> True

ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)

getPaymentOutput : Address -> ScriptContext -> Maybe TxOut
getPaymentOutput adr record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) } = Nothing
getPaymentOutput adr record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) }
  = if adr == txOutAddress txO && (Payment x) == txOutDatum txO  then Just txO else getPaymentOutput adr (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) })
getPaymentOutput adr record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) } = Nothing


checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt st ctx = case getPaymentOutput (owner st) ctx of λ {
  Nothing -> False ;
  (Just tx) -> ratioCompare amt (txOutValue tx) (ratio st) }


{-# COMPILE AGDA2HS checkPayment #-}

{-
aux2 : (x w : Maybe ℤ) →
    x ≡ w → {a b : ℤ}
    (pf : not ((case w of λ { Nothing → false ; (Just v) → true })) ≡ true) →
    a ≡ b
aux2 x w p pf = {!!} -}

{-
checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt st ctx = case getPaymentOutput (owner st) ctx of λ where
  Nothing -> False
  (Just txO) -> ratioCompare amt (txOutValue txO) (ratio st)
-}

checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = case getPaymentOutput pkh ctx of λ where
  Nothing -> False
  (Just txO) -> (txOutValue txO) == amt


{-# COMPILE AGDA2HS checkBuyer #-}
                             

checkClose : Params -> Label -> ScriptContext -> Bool
checkClose par st ctx = case getPaymentOutput (owner st) ctx of λ where
  Nothing -> False
  (Just txO) -> (txOutValue txO) == oldValue ctx


maybe+ : Maybe Value -> Value -> Value
maybe+ Nothing v = v
maybe+ (Just x) v = x + v

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par st red ctx = case red of λ where
  (Update amt r) -> checkSigned (owner st) ctx &&
                    checkRational r &&
                    newValue ctx == Just amt &&
                    newLabel ctx == Just (record {ratio = r ; owner = owner st}) &&
                    continuing ctx
  (Exchange amt pkh) -> oldValue ctx == (maybe+ (newValue ctx) amt) &&
                        newLabel ctx == Just st &&
                        checkPayment par amt st ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx
  Close -> not (continuing ctx) &&
           checkSigned (owner st) ctx --checkClose par st ctx


{-# COMPILE AGDA2HS agdaValidator #-}
           

