open import Haskell.Prelude
open import Lib
open import Value

module Validators.DEx where


checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

record Info : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
open Info public

eqInfo : Info -> Info -> Bool
eqInfo b c = (ratio b == ratio c) &&
             (owner b == owner c)

instance
  iEqInfo : Eq Info
  iEqInfo ._==_ = eqInfo


Label = (AssetClass × Info)
{-# COMPILE AGDA2HS Label #-}


open import ScriptContext Label Value


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


checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = (assetClassValueOf (oldValue ctx) tok) == 1

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = (assetClassValueOf (newValue ctx) tok) == 1


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

checkPayment : Params -> Integer -> Info -> ScriptContext -> Bool
checkPayment par amt l ctx = payAdr ctx == owner l &&
                             ratioCompare amt (assetClassValueOf (payVal ctx) (buyC par)) (ratio l) &&
                             checkMinValue (payVal ctx)

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = MkMap ((ac , amt) ∷ [])

checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = buyAdr ctx == pkh &&
                             assetClassValueOf (buyVal ctx) (sellC par) == amt &&
                             checkMinValue (buyVal ctx)

{-# COMPILE AGDA2HS checkBuyer #-}
{-# COMPILE AGDA2HS checkPayment #-}
{-# COMPILE AGDA2HS processPayment #-}
{-# COMPILE AGDA2HS ratioCompare #-}

{-# COMPILE AGDA2HS checkTokenBurned #-}


agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
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

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatum ctx) of λ where
  (tok , l) -> ownAssetClass ctx == tok && checkRational (ratio l)

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = checkTokenOut (ownAssetClass ctx) ctx

isInitial : Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx = consumes oref ctx &&
                          checkDatum addr ctx &&
                          checkValue addr ctx


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




