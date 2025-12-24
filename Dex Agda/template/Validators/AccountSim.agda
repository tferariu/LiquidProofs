open import Haskell.Prelude hiding (lookup)
open import Lib
open import Value

module Validators.AccountSim where

-- Defining the types of our Plinth Datum, referred to as Label in Agda
AccMap = List (PubKeyHash × Value)

Label = (AssetClass × AccMap)

{-# COMPILE AGDA2HS AccMap #-}
{-# COMPILE AGDA2HS Label #-}

-- The abstract ScriptContext
record ScriptContext : Set where
    field     
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Label
        payments      : List (PubKeyHash × Value)
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokCurrSymbol : CurrencySymbol
        tokenIn       : Bool
        tokenOut      : Bool
        validInterval : Interval

-- Functions equivalent to Plinth ScriptContext functions or provided by our template
--https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-ledger-api/PlutusLedgerApi-V3-Data-Contexts.html#t:ScriptContext

newDatum : ScriptContext -> Label
newDatum ctx = ScriptContext.outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = ScriptContext.continues ctx

getPayment' : PubKeyHash -> List (PubKeyHash × Value) -> Value
getPayment' pkh [] = emptyValue
getPayment' pkh ((pkh' , v) ∷ xs) = if pkh == pkh' then v else getPayment' pkh xs

getPayment : PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = getPayment' pkh (ScriptContext.payments ctx)

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = ScriptContext.mint ctx 

ownAssetClass : TokenName -> ScriptContext -> AssetClass
ownAssetClass tn ctx = ((ScriptContext.tokCurrSymbol ctx) , tn)

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn ac = ScriptContext.tokenIn

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut ac = ScriptContext.tokenOut
        
checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == ScriptContext.signature ctx

sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = ScriptContext.mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == ScriptContext.inputRef ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = ScriptContext.continues ctx

newDatumAddr : Address -> ScriptContext -> Label
newDatumAddr adr ctx = newDatum ctx

newValueAddr : Address -> ScriptContext -> Value
newValueAddr adr ctx = newValue ctx

checkTokenOutAddr : Address -> AssetClass -> ScriptContext -> Bool
checkTokenOutAddr adr = checkTokenOut

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = getPayment pkh ctx == v

before : POSIXTime -> Interval -> Bool
before record { getPOSIXTime = time } (start , end) = time < start

after : POSIXTime -> Interval -> Bool
after record { getPOSIXTime = time } (start , end) = time > end

validRange : ScriptContext -> Interval
validRange ctx = ScriptContext.validInterval ctx

-- The type of the Plinth Redeemer, referred to as Input in Agda
data Input : Set where
  Open     : PubKeyHash -> Input
  Close    : PubKeyHash -> Input
  Withdraw : PubKeyHash -> Value -> Input
  Deposit  : PubKeyHash -> Value -> Input
  Transfer : PubKeyHash -> PubKeyHash -> Value -> Input
  Cleanup  : Input

{-# COMPILE AGDA2HS Input #-}

-- Helper functions of the validator
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

lookup : PubKeyHash -> AccMap -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x , y) ∷ xs) = if (pkh == x)
  then Just y
  else lookup pkh xs

{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS delete #-}
{-# COMPILE AGDA2HS lookup #-}

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
checkTransfer tok (Just vF) (Just vT) from to val lab ctx = geq val emptyValue && geq vF val && from /= to &&
                         newDatum ctx == (tok , insert from (vF - val) (insert to (vT + val) lab))

{-# COMPILE AGDA2HS checkMembership #-}
{-# COMPILE AGDA2HS checkEmpty #-}
{-# COMPILE AGDA2HS checkWithdraw #-}
{-# COMPILE AGDA2HS checkDeposit #-}
{-# COMPILE AGDA2HS checkTransfer #-}

-- The Validator
agdaValidator : Label -> Input -> ScriptContext -> Bool
agdaValidator (tok , lab) inp ctx = checkTokenIn tok ctx && (case inp of λ where

    (Open pkh) -> checkTokenOut tok ctx && continuing ctx && checkSigned pkh ctx &&
                  not (checkMembership (lookup pkh lab)) &&
                  newDatum ctx == (tok , insert pkh emptyValue lab) && newValue ctx == oldValue ctx

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

-- Helper functions of the Minting Policy Script
checkDatum : Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx = case (newDatumAddr addr ctx) of λ where
  (tok , map) -> ownAssetClass tn ctx == tok && map == []

checkValue : Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx && newValueAddr addr ctx == minValue

isInitial : Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial addr oref tn ctx = consumes oref ctx &&
                          checkDatum addr tn ctx &&
                          checkValue addr tn ctx


{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS isInitial #-}

-- The Thread Token Minting Policy
agdaPolicy : Address -> TxOutRef -> TokenName -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         isInitial addr oref tn ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
  else False
  where
    amt = getMintedAmount ctx

{-# COMPILE AGDA2HS agdaPolicy #-}

