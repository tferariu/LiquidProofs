module DEx2 where

open import Haskell.Prelude




record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 

ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b

instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational
  
checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

PubKeyHash = Nat
AssetClass = Nat

record Label : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
open Label public
{-# COMPILE AGDA2HS Label #-}


Datum = (AssetClass × Label)

open import Lib (Datum)

eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel



data Input : Set where
  Update   : Value -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input
  Start    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}





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



checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = buyTo ctx == pkh &&
                             assetClassValueOf (buyVal ctx) (sellC par) == amt &&
                             checkMinValue (buyVal ctx)
                             --buyAmt ctx == amt

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
           not (checkTokenOut (newDatum ctx .fst) ctx) && checkSigned (owner lab) ctx 
  Start -> False)
           


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


agdaPolicy : Address -> TxOutRef -> Input -> ScriptContext -> Bool
agdaPolicy addr oref red ctx = case red of λ where
  (Update v r) -> False
  (Exchange amt pkh) -> False 
  Close -> not (continuingAddr addr ctx) &&
           getMintedAmount ctx == -1
  Start -> continuingAddr addr ctx &&
           isInitial addr oref ctx &&
           getMintedAmount ctx == 1

{-
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx
-}

{-# COMPILE AGDA2HS agdaPolicy #-}

