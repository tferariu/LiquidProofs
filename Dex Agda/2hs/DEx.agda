module DEx where

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

AssetClass = Nat --CurrencySymbol × TokenName
TxOutRef = Nat

{-
record Value : Set where
    field
            amount   : Integer
            currency : AssetClass
open Value public
-}

data Map (A B : Set) : Set where
 MkMap : List (A × B) -> Map A B

Value = Map AssetClass Integer
--Value = List (AssetClass × Integer)

addValue : Value -> Value -> Value
addValue (MkMap []) (MkMap []) = MkMap []
addValue (MkMap []) (MkMap (v ∷ vs)) = MkMap (v ∷ vs)
addValue (MkMap (v ∷ vs)) (MkMap []) = MkMap (v ∷ vs)
addValue (MkMap ((ac , val) ∷ xs)) (MkMap ((ac' , val') ∷ ys)) 
  = if (ac == ac') then addValue (MkMap xs) (MkMap ((ac , val + val') ∷ ys)) --MkMap ((ac , val + val') ∷ (addValue ? ?))
                   else if (ac < ac') then {!!} --MkMap (ac , val) ∷ (addValue xs v2)
                                       else {!!} --MkMap (ac' , val') ∷ (addValue v1 ys)) 
{-
addValue : Value -> Value -> Value
addValue [] [] = []
addValue [] (v ∷ vs) = v ∷ vs
addValue (v ∷ vs) [] = v ∷ vs
addValue v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val + val') ∷ (addValue xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValue xs v2)
                                       else (ac' , val') ∷ (addValue v1 ys))-}

{-
addValue : Value -> Value -> Value
addValue a b = case currency a == currency b of λ where
  True -> record { amount = amount a + amount b ; currency = currency a }
  False -> a
-}

{-
eqValue : Value -> Value -> Bool
eqValue a b = (amount a == amount b) &&
              (currency a == currency b) -}

instance
--  iEqValue : Eq Value
--  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue


record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r

--make this be given to you by the type system
checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

Cmap = List ((Rational × PubKeyHash) × Integer)

--rename to datum maybe?
record Label : Set where
  field
  -- value ??
    ratio  : Rational
    owner  : PubKeyHash
open Label public

Datum = (AssetClass × Label)
{-
record Datum : Set where
  field
    tok   : AssetClass
    label : Label
open Label public-}


{-# COMPILE AGDA2HS Label #-}

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

 -- iOrdRational : Ord Rational
 -- iOrdRational = ordFromLessThan ltRational


eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)


instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel


data OutputDatum : Set where

  Payment : Address -> OutputDatum
  Script : Datum -> OutputDatum


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
  Minting : AssetClass -> ScriptPurpose
  Both : Address -> AssetClass -> ScriptPurpose

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
        inputRef    : TxOutRef
        mint        : Value
        
        
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
            -- why not owner? -- write this justification in notes
open Params public

{-# COMPILE AGDA2HS Params #-}

getContinuingOutputs : ScriptContext -> List TxOut
getContinuingOutputs record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint } = []
getContinuingOutputs record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) ; inputRef = inputRef ; mint = mint } = if adr == txOutAddress txO
  then txO ∷ getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) ; inputRef = inputRef ; mint = mint })
  else getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) ; inputRef = inputRef ; mint = mint })
getContinuingOutputs record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Both x t) ; inputRef = inputRef ; mint = mint } = []
getContinuingOutputs record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Both adr t) ; inputRef = inputRef ; mint = mint } = if adr == txOutAddress txO
  then txO ∷ getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) ; inputRef = inputRef ; mint = mint })
  else getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Spending adr) ; inputRef = inputRef ; mint = mint })
getContinuingOutputs record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) ; inputRef = inputRef ; mint = mint } = []

{-record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending x) }
  = []
getContinuingOutputs record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending adr) }
  = if adr == txOutAddress txO
       then txO ∷ getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                                 ; signature = signature ; purpose = Spending adr })
       else getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                           ; signature = signature ; purpose = Spending adr })
getContinuingOutputs record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Minting x) }
  = []
-}




ownOutput : AssetClass -> ScriptContext -> TxOut
ownOutput tok ctx = {!!}

{-case (getContinuingOutputs ctx) of λ where
  (o ∷ []) -> o
  _ -> record { txOutAddress = 0 ; txOutValue = [] ; txOutDatum = Payment 0 }-}

--record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 } ; txOutDatum = Payment 0 }
{-

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newDatum : AssetClass -> ScriptContext -> Datum
newDatum tok ctx = case txOutDatum (ownOutput tok ctx) of λ where
  (Script x) -> x
  _ -> 0 , (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 })

--record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }

newValue : AssetClass -> ScriptContext -> Value
newValue tok ctx = txOutValue (ownOutput tok ctx)

aux : List TxOut -> Bool
aux txs = case txs of λ {
  (o ∷ []) -> True ;
  _ -> False }

continuing : ScriptContext -> Bool
continuing ctx = aux (getContinuingOutputs ctx)
  
ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)


{-
getPaymentOutput : Address -> ScriptContext -> TxOut
getPaymentOutput adr record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = purpose ; inputRef = inputRef ; mint = mint } = {!!}
-}

{-adr record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) }
  = {!!} {-record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
           ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }-}
getPaymentOutput adr record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending x) }
  = if txOutAddress txO == adr && txOutDatum txO == (Payment x)
       then txO
       else getPaymentOutput adr (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                 ; signature = signature ; purpose = (Spending x) })
getPaymentOutput adr record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Minting x) }
  = {!!} {-record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
           ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }-}
-}

aux' : ScriptPurpose -> Address
aux' p = case p of λ where
  (Minting cs) -> 0
  (Spending adr) -> adr
  (Both adr cs) -> adr

getSelf : ScriptContext -> Address
getSelf ctx = aux' (purpose ctx) 

processPayment : AssetClass -> Integer -> Rational -> Value -> Bool
processPayment ac amt r [] = False
processPayment ac amt r ((ac' , amt') ∷ vs)
  = if ac == ac'
  then ratioCompare amt amt' r
  else processPayment ac amt r vs

checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint } = False
checkPayment par amt l record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint }
  = if txOutAddress txO == (owner l) && txOutDatum txO == (Payment x)
    then processPayment (buyC par) amt (ratio l) (txOutValue txO)
    else checkPayment par amt l (record { txOutputs = (txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint })
checkPayment par amt l record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) ; inputRef = inputRef ; mint = mint } = False


{-txOutAddress (getPaymentOutput (owner l) ctx) == owner l &&
e                                 --ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l) &&
                                 --currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par &&
                                 txOutDatum (getPaymentOutput (owner l) ctx) == Payment (getSelf ctx)-}


{-# COMPILE AGDA2HS checkPayment #-}



processBuyer : AssetClass -> Integer -> Value -> Bool
processBuyer ac amt [] = False
processBuyer ac amt ((ac' , amt') ∷ vs)
  = if ac == ac'
  then amt == amt'
  else processBuyer ac amt vs

checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint } = False
checkBuyer par amt pkh record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint }
  = if txOutAddress txO == pkh && txOutDatum txO == (Payment x)
    then processBuyer (sellC par) amt (txOutValue txO) 
    else checkBuyer par amt pkh (record { txOutputs = (txOutputs) ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) ; inputRef = inputRef ; mint = mint })
checkBuyer par amt pkh record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = (Minting x) ; inputRef = inputRef ; mint = mint } = False
{-
checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = txOutAddress (getPaymentOutput pkh ctx) == pkh &&
                             --(txOutValue (getPaymentOutput pkh ctx)) ==
                             --record { amount = amt ; currency = sellC par }  &&
                             txOutDatum (getPaymentOutput pkh ctx) == Payment (getSelf ctx)
-}

{-# COMPILE AGDA2HS checkBuyer #-}


checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok record { txOutputs = txOutputs ; inputVal = [] ; signature = signature ; purpose = purpose ; inputRef = inputRef ; mint = mint } = False
checkTokenIn tok record { txOutputs = txOutputs ; inputVal = ((ac , amt) ∷ inputVal) ; signature = signature ; purpose = purpose ; inputRef = inputRef ; mint = mint } = if tok == ac then amt == 1
  else checkTokenIn tok record { txOutputs = txOutputs ; inputVal = (inputVal) ; signature = signature ; purpose = purpose ; inputRef = inputRef ; mint = mint } 

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = {!!} --hasTokenOut ctx

agdaValidator : Params -> Datum -> Input -> ScriptContext -> Bool
agdaValidator par (tok , l) red ctx = checkTokenIn tok ctx &&
                                      (case red of λ where
  (Update amt r) -> checkSigned (owner l) ctx &&
                    checkRational r &&
                    --newValue ctx == record { amount = amt ; currency = sellC par } && 
                    newDatum tok ctx == (tok , (record { ratio = r ; owner = owner l })) &&
                    continuing ctx
  (Exchange amt pkh) -> oldValue ctx == addValue {-!!!-} (newValue tok ctx) (((sellC par) , amt) ∷ []) && 
                        newDatum tok ctx == (tok , l) &&
                        checkPayment par amt l ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx
  Close -> not (continuing ctx) &&
           checkSigned (owner l) ctx)
--record { amount = amt ; currency = sellC par }

{-# COMPILE AGDA2HS agdaValidator #-} 


getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = {!!} --mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = {!!} --tokAssetClass ctx

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = {!!}
{-case (newDatum tok ctx) of λ where
  (tok , _) -> ownAssetClass ctx == tok
  (tok , _) -> False-}

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = {!!} --hasTokenOut ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = True --continues ctx

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}




{-
aux2 : List TxOut -> Bool
aux2 txs = case txs of λ {
  [] -> True ;
  _ -> False }

checkClose : ScriptContext -> Bool
checkClose ctx = aux2 (getContinuingOutputs ctx) -}




{-
postulate reduceErr : {f : Set -> Set} -> f err ≡ err
postulate impossible : {a : Bool} -> err ≡ True -> ⊥ --True ≡ False
-}

postulate err : {a : Set} -> a

--postulate impossible : {a : Set} {b : a}  {{_ : Eq a}} -> (err {a} == b) ≡ False


foo : List Nat -> Bool
foo [] = err
foo (x ∷ []) = True
foo (x ∷ y ∷ l) = err

validator : List Nat -> String -> Bool
validator ns str = foo ns && str == "foo"
{-
bar : {n : List Nat} {str : String} -> n ≡ [] -> validator n str ≡ False
bar {.[]} {str = str} refl = {!!}-}

--model mathematically Maybe, Notining = False
-- pretend there are no errors  <-!

--rewrite impossible {Nat} {5} {{ {!!} }} = {!!} --refl


{-
addValue : Value -> Value -> Value
addValue a b = {!!}

subValue : Value -> Value -> Value
subValue a b = {!!}

mulValue : Value -> Value -> Value
mulValue a b = {!!}

negateValue : Value -> Value
negateValue a = {!!}

absValue : Value -> Value
absValue a = {!!}


signValue : Value -> Value
signValue a = {!!}

instance
  iNumValue : Num Value
  iNumValue .MinusOK _ _ = ⊤
  iNumValue .NegateOK _          = ⊤
  iNumValue .Num.FromIntegerOK _ = ⊤
  iNumValue ._+_ x y             = addValue x y
  iNumValue ._-_ x y             = subValue x y
  iNumValue ._*_ x y             = mulValue x y
  iNumValue .negate x            = negateValue x
  iNumValue .abs x               = absValue x
  iNumValue .signum x            = signValue x
  iNumValue .fromInteger n       = {!!}
-}

{-
  iOrdRational : Ord Rational
  iOrdRational = ordFromLessThan ltRational
-}

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
-}
