module DExpanded2 where

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

getContinuingOutputs : ScriptContext -> List TxOut
getContinuingOutputs record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) } = []
getContinuingOutputs record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) }
  = if adr == txOutAddress txO
       then txO ∷ getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending adr })
       else getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending adr })
getContinuingOutputs record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) } = []


ownOutput : ScriptContext -> TxOut
ownOutput ctx = case (getContinuingOutputs ctx) of λ where
  (o ∷ []) -> o
  _ -> record { txOutAddress = 0 ; txOutValue = -1 ; txOutDatum = Payment 0 }

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx


newLabel : ScriptContext -> Label
newLabel ctx = case txOutDatum (ownOutput ctx) of λ where
  (Script x) -> x
  _ -> record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }

newValue : ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

continuing : ScriptContext -> Bool
continuing ctx = case (getContinuingOutputs ctx) of λ where
  (o ∷ []) -> True
  _ -> False
  
ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)


getPaymentOutput : Address -> ScriptContext -> TxOut
getPaymentOutput adr record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) }
  = record { txOutAddress = 0 ; txOutValue = -1 ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }
getPaymentOutput adr record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) }
  = if adr == txOutAddress txO && (Payment x) == txOutDatum txO
       then txO
       else getPaymentOutput adr (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) })
getPaymentOutput adr record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) }
  = record { txOutAddress = 0 ; txOutValue = -1 ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }


{-
checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l ctx = ratioCompare amt (txOutValue (getPaymentOutput (owner l) ctx)) (ratio l) 
-}

---!!!!! ASSET CLASS

checkPayment : Params -> Integer -> Label -> PubKeyHash -> ScriptContext -> Bool
checkPayment par amt l pkh ctx = txOutAddress (getPaymentOutput (owner l) ctx) == owner l &&
                                 ratioCompare amt (txOutValue (getPaymentOutput (owner l) ctx)) (ratio l) 
                                 
{--}


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
checkBuyer par amt pkh ctx = txOutAddress (getPaymentOutput pkh ctx) == pkh &&
                             (txOutValue (getPaymentOutput pkh ctx)) == amt


{-# COMPILE AGDA2HS checkBuyer #-}
                             

checkClose : Params -> Label -> ScriptContext -> Bool
checkClose par st ctx = (txOutValue (getPaymentOutput (owner st) ctx)) == oldValue ctx


maybe+ : Maybe Value -> Value -> Value
maybe+ Nothing v = v
maybe+ (Just x) v = x + v


agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par l red ctx = case red of λ where
  (Update amt r) -> checkSigned (owner l) ctx &&
                    checkRational r &&
                    newValue ctx == amt &&
                    newLabel ctx == (record {ratio = r ; owner = owner l}) &&
                    continuing ctx
  (Exchange amt pkh) -> oldValue ctx == (newValue ctx) + amt &&
                        newLabel ctx == l &&
                        checkPayment par amt l pkh ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx
  Close -> not (continuing ctx) &&
           checkSigned (owner l) ctx --checkClose par st ctx


{-# COMPILE AGDA2HS agdaValidator #-} 
           

