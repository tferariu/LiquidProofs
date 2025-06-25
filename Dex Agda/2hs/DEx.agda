module DEx where

open import Haskell.Prelude

variable
  k v : Set

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Nat
TokenName = Nat

PubKeyHash = Nat 

AssetClass = Nat

Address = Nat
TxOutRef = Nat

data Map (A B : Set) : Set where
 MkMap : List (A × B) -> Map A B

Value = Map AssetClass Integer
--Value = List (AssetClass × Integer)

{-
addSingleton : (AssetClass × Integer) -> Value -> Value
addSingleton (ac , val) (MkMap []) = MkMap ((ac , val) ∷ [])
addSingleton (ac , val) (MkMap ((ac' , val') ∷ vs)) = {!!}-}

addValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val + val') ∷ (addValueAux xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValueAux xs v2)
                                       else (ac' , val') ∷ (addValueAux v1 ys))

addValue : Value -> Value -> Value
addValue (MkMap v1) (MkMap v2) = MkMap (addValueAux v1 v2)


{-
addValue (MkMap []) (MkMap []) = MkMap []
addValue (MkMap []) (MkMap (v ∷ vs)) = MkMap (v ∷ vs)
addValue (MkMap (v ∷ vs)) (MkMap []) = MkMap (v ∷ vs)
addValue (MkMap ((ac , val) ∷ xs)) (MkMap ((ac' , val') ∷ ys)) 
  = if (ac == ac') then addValue (MkMap xs) (MkMap ((ac , val + val') ∷ ys)) --MkMap ((ac , val + val') ∷ (addValue ? ?))
                   else if (ac < ac') then {!!} --MkMap (ac , val) ∷ (addValue xs v2)
                                       else {!!} --MkMap (ac' , val') ∷ (addValue v1 ys)) -}
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


eqValue : Value -> Value -> Bool
eqValue (MkMap v1) (MkMap v2) = v1 == v2

ltVal : Value -> Value -> Bool
ltVal (MkMap v1) (MkMap v2) = v1 < v2 

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

  iOrdFromLessThanValue : OrdFromLessThan Value
  iOrdFromLessThanValue .OrdFromLessThan._<_ = ltVal

  iOrdVal : Ord Value
  iOrdVal = record
    { OrdFromLessThan iOrdFromLessThanValue }

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

record Label : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
open Label public
{-# COMPILE AGDA2HS Label #-}


Datum = (AssetClass × Label)

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

--  iOrdRational : Ord Rational
--  iOrdRational = ordFromLessThan ltRational


eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel

record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Datum
        payTo         : PubKeyHash
        payVal        : Value
        buyTo         : PubKeyHash
        buyVal        : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
open ScriptContext public


checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx


data Input : Set where
  Update   : Value -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}

--newLabel : ScriptContext -> Label
--newLabel ctx = outputLabel ctx

newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

--emptyValue : Value
--emptyValue = 0

ada : AssetClass
ada = 0

minValue : Value
minValue = MkMap ((ada , 2) ∷ [])

assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (MkMap []) ac = 0
assetClassValueOf (MkMap ((ac' , amt) ∷ vs)) ac = if ac' == ac then amt else assetClassValueOf (MkMap vs) ac

--checkValue : Value -> Bool
--checkValue v = v >= minValue

checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 2

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = (assetClassValueOf (inputVal ctx) tok) == 1

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = (assetClassValueOf (outputVal ctx) tok) == 1

{-# COMPILE AGDA2HS checkMinValue #-}
{-# COMPILE AGDA2HS checkTokenIn #-}
{-# COMPILE AGDA2HS checkTokenOut #-}

ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)

processPayment : AssetClass -> Integer -> Rational -> Value -> Bool
processPayment ac amt r (MkMap []) = False
processPayment ac amt r (MkMap ((ac' , amt') ∷ vs))
  = if ac == ac'
  then ratioCompare amt amt' r
  else processPayment ac amt r (MkMap vs)

checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l ctx = payTo ctx == owner l &&
                             ratioCompare amt (assetClassValueOf (payVal ctx) (buyC par)) (ratio l) &&
                             checkMinValue (payVal ctx)
                              --ratioCompare amt (payAmt ctx) (ratio st)
                              --processPayment (buyC par) amt (ratio l) (payVal ctx) &&

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = MkMap ((ac , amt) ∷ [])

checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = buyTo ctx == pkh &&
                             assetClassValueOf (buyVal ctx) (sellC par) == amt &&
                             checkMinValue (buyVal ctx)
                             --buyAmt ctx == amt

{-# COMPILE AGDA2HS checkBuyer #-}
{-# COMPILE AGDA2HS checkPayment #-}
{-# COMPILE AGDA2HS processPayment #-}
{-# COMPILE AGDA2HS ratioCompare #-}

{-
checkClose : Params -> Label -> ScriptContext -> Bool
checkClose par st ctx = payTo ctx == owner st &&
                        payVal ctx == oldValue ctx
-}

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1

{-# COMPILE AGDA2HS checkTokenBurned #-}


agdaValidator : Params -> Datum -> Input -> ScriptContext -> Bool
agdaValidator par (tok , lab) red ctx = checkTokenIn tok ctx && (case red of λ where
  (Update v r) -> checkSigned (owner lab) ctx &&
                    checkRational r && checkMinValue v &&
                    newValue ctx == v &&
                    newDatum ctx == (tok , record {ratio = r ; owner = owner lab}) &&
                    continuing ctx && checkTokenOut tok ctx
  (Exchange amt pkh) -> oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt) &&
                        newDatum ctx == (tok , lab) &&
                        checkPayment par amt lab ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx && checkTokenOut tok ctx
  Close -> not (continuing ctx) && checkTokenBurned tok ctx &&
           not (checkTokenOut (newDatum ctx .fst) ctx) && checkSigned (owner lab) ctx )
           
{-# COMPILE AGDA2HS agdaValidator #-}

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatum ctx) of λ where
  (tok , l) -> ownAssetClass ctx == tok && checkRational (ratio l)
  --(tok , (Collecting _ _ _ _)) -> False

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = checkTokenOut (ownAssetClass ctx) ctx --hasTokenOut ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx

{-# COMPILE AGDA2HS consumes #-}
{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS isInitial #-}
{-# COMPILE AGDA2HS continuingAddr #-}

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx


{-# COMPILE AGDA2HS agdaPolicy #-}




