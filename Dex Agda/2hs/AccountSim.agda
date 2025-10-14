{-# OPTIONS --erased-matches #-}

module AccountSim where

open import Haskell.Prelude

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

Address = Nat

PubKeyHash = Nat
Value = Integer
TxOutRef = Nat
AssetClass = Nat

AccMap = List (PubKeyHash × Value)

Label = (AssetClass × AccMap)

{-# COMPILE AGDA2HS AccMap #-}
{-# COMPILE AGDA2HS Label #-}


record ScriptContext : Set where
    field
        inputVal      : Integer
        outputVal     : Integer
        outputDatum   : Label
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
  Cleanup  : Input

{-# COMPILE AGDA2HS Input #-}


insert : PubKeyHash -> Value -> AccMap -> AccMap
insert pkh val [] = ((pkh , val) ∷ [])
insert pkh val ((x , y) ∷ xs) = if (pkh == x)
  then ((pkh , val) ∷ xs)
  else ((x , y) ∷ (insert pkh val xs))
  
delete : PubKeyHash -> AccMap -> AccMap
delete pkh [] = []
delete pkh ((x , y) ∷ xs) = if (pkh == x)
  then xs
  else ((x , y) ∷ (delete pkh xs))

{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS delete #-}

newDatum : ScriptContext -> Label
newDatum ctx = outputDatum ctx

newToken : ScriptContext -> AssetClass
newToken ctx = fst (outputDatum ctx)

newLabel : ScriptContext -> AccMap
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

checkMembership' : PubKeyHash -> AccMap -> Bool
checkMembership' pkh lab = case lookup pkh lab of λ where
  Nothing -> False
  (Just v) -> True

checkMembership : Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

checkEmpty : Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

checkWithdraw : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val lab ctx = geq val emptyValue && geq v val && (newDatum ctx == (tok , insert pkh (v - val) lab))

checkDeposit : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val lab ctx = geq val emptyValue && (newDatum ctx == (tok , insert pkh (v + val) lab))

checkTransfer : AssetClass -> Maybe Value -> Maybe Value -> PubKeyHash -> PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val lab ctx = geq val 0 && geq vF val && from /= to &&
                         newDatum ctx == (tok , insert from (vF - val) (insert to (vT + val) lab))


checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == -1

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

agdaValidator : Label -> Input -> ScriptContext -> Bool
agdaValidator (tok , lab) inp ctx = checkTokenIn tok ctx && (case inp of λ where

    (Open pkh) -> checkTokenOut tok ctx && continuing ctx && checkSigned pkh ctx &&
                  not (checkMembership (lookup pkh lab)) &&
                  newDatum ctx == (tok , insert pkh 0 lab) && newValue ctx == oldValue ctx

    (Close pkh) -> checkTokenOut tok ctx && continuing ctx && checkSigned pkh ctx && checkEmpty (lookup pkh lab) &&
                   newDatum ctx == (tok , delete pkh lab) && newValue ctx == oldValue ctx

    (Withdraw pkh val) -> checkTokenOut tok ctx && continuing ctx && checkSigned pkh ctx &&
                          checkWithdraw tok (lookup pkh lab) pkh val lab ctx &&
                          newValue ctx + val == oldValue ctx

    (Deposit pkh val) -> checkTokenOut tok ctx && continuing ctx && checkSigned pkh ctx &&
                         checkDeposit tok (lookup pkh lab) pkh val lab ctx &&
                         newValue ctx == oldValue ctx + val

    (Transfer from to val) -> checkTokenOut tok ctx && continuing ctx && checkSigned from ctx &&
                              checkTransfer tok (lookup from lab) (lookup to lab) from to val lab ctx &&
                              newValue ctx == oldValue ctx 

    Cleanup -> checkTokenBurned tok ctx && not (checkTokenOut tok ctx) && not (continuing ctx) && lab == [] )

{-# COMPILE AGDA2HS agdaValidator #-}


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
checkValue addr ctx = newValue ctx == 0 && hasTokenOut ctx

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

