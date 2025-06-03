module AccountSim where

open import Haskell.Prelude

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

Address = Nat

PubKeyHash = Integer
Value = Integer
TxOutRef = Nat
AssetClass = Nat

Label = List (PubKeyHash × Value)

Datum = (AssetClass × Label)

{-# COMPILE AGDA2HS Label #-}
{-# COMPILE AGDA2HS Datum #-}


record ScriptContext : Set where
    field
        inputVal      : Integer
        outputVal     : Integer
        outputDatum   : Datum
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        hasTokenIn    : Bool
        hasTokenOut   : Bool
        mint          : Integer
        tokAssetClass : AssetClass
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

newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

newToken : ScriptContext -> AssetClass
newToken ctx = fst (outputDatum ctx)

newLabel : ScriptContext -> Label
newLabel ctx = snd (outputDatum ctx)

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

minValue : Value
minValue = 2

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = pkh == signature ctx

aux : Maybe Value -> Bool
aux Nothing = False
aux (Just _) = True

checkMembership' : PubKeyHash -> Label -> Bool
checkMembership' pkh lab = case lookup pkh lab of λ where
  Nothing -> False
  (Just v) -> True

checkMembership : Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

checkEmpty : Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

checkWithdraw : Maybe Value -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkWithdraw Nothing _ _ _ _ = False
checkWithdraw (Just v) pkh val lab ctx = geq val emptyValue && geq v val && (newLabel ctx == insert pkh (v - val) lab)

checkDeposit : Maybe Value -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkDeposit Nothing _ _ _ _ = False
checkDeposit (Just v) pkh val lab ctx = geq val emptyValue && (newLabel ctx == insert pkh (v + val) lab)

checkTransfer : Maybe Value -> Maybe Value -> PubKeyHash -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkTransfer Nothing _ _ _ _ _ _ = False
checkTransfer (Just vF) Nothing _ _ _ _ _ = False
checkTransfer (Just vF) (Just vT) from to val lab ctx = geq val 0 && geq vF val && from /= to &&
                         newLabel ctx == insert from (vF - val) (insert to (vT + val) lab)
{-
checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx-}

{-# COMPILE AGDA2HS checkMembership #-}
{-# COMPILE AGDA2HS checkEmpty #-}
{-# COMPILE AGDA2HS checkWithdraw #-}
{-# COMPILE AGDA2HS checkDeposit #-}
{-# COMPILE AGDA2HS checkTransfer #-}
--{-# COMPILE AGDA2HS checkPayment #-}

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = hasTokenIn ctx

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = hasTokenOut ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

agdaValidator : Datum -> Input -> ScriptContext -> Bool
agdaValidator (tok , lab) inp ctx = checkTokenIn tok ctx && checkTokenOut tok ctx && continuing ctx &&
                                    newToken ctx == tok && (case inp of λ where

    (Open pkh) -> checkSigned pkh ctx && not (checkMembership (lookup pkh lab)) &&
                  newLabel ctx == insert pkh 0 lab && newValue ctx == oldValue ctx

    (Close pkh) -> checkSigned pkh ctx && checkEmpty (lookup pkh lab) &&
                   newLabel ctx == delete pkh lab && newValue ctx == oldValue ctx

    (Withdraw pkh val) -> checkSigned pkh ctx && checkWithdraw (lookup pkh lab) pkh val lab ctx &&
                          newValue ctx == oldValue ctx - val

    (Deposit pkh val) -> checkSigned pkh ctx && checkDeposit (lookup pkh lab) pkh val lab ctx &&
                         newValue ctx == oldValue ctx + val

    (Transfer from to val) -> checkSigned from ctx &&
                              checkTransfer (lookup from lab) (lookup to lab) from to val lab ctx &&
                              newValue ctx == oldValue ctx )

{-# COMPILE AGDA2HS agdaValidator #-}

--use function composition?

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = mint ctx 

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

ownAssetClass : ScriptContext -> AssetClass
ownAssetClass ctx = tokAssetClass ctx

checkDatum : Address -> ScriptContext -> Bool
checkDatum addr ctx = case (newDatum ctx) of λ where
  (tok , map) -> ownAssetClass ctx == tok && map == []

checkValue : Address -> ScriptContext -> Bool
checkValue addr ctx = hasTokenOut ctx

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
{-# COMPILE AGDA2HS getMintedAmount #-}

agdaPolicy : Address -> TxOutRef -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

