module Validators.DEx where

import Lib (Address, AssetClass, PubKeyHash, Rational, TokenName, TxOutRef, denominator, numerator)
import Value (Value, assetClassValue, assetClassValueOf, checkMinValue)

data Info = Info{ratio :: Rational, owner :: PubKeyHash}

type Label = (AssetClass, Info)

data Input = Update Value Rational
           | Exchange Integer PubKeyHash
           | Close

data Params = Params{sellC :: AssetClass, buyC :: AssetClass}

checkRational :: Rational -> Bool
checkRational r = numerator r >= 0 && denominator r > 0

ratioCompare :: Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * numerator r <= b * denominator r

checkPaymentRatio ::
                  PubKeyHash ->
                    Integer -> AssetClass -> Rational -> ScriptContext -> Bool
checkPaymentRatio pkh amt ac r ctx
  = ratioCompare amt (assetClassValueOf (getPayments pkh ctx) ac) r
      && checkMinValue (getPayments pkh ctx)

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case red of
          Update v r -> checkSigned (owner lab) ctx &&
                          checkRational r &&
                            checkMinValue v &&
                              newValue ctx == v &&
                                newDatum ctx == (tok, Info r (owner lab)) &&
                                  continuing ctx && checkTokenOut tok ctx
          Exchange amt pkh -> oldValue ctx ==
                                newValue ctx + assetClassValue (sellC par) amt
                                &&
                                newDatum ctx == (tok, lab) &&
                                  checkPaymentRatio (owner lab) amt (buyC par) (ratio lab) ctx &&
                                    continuing ctx && checkTokenOut tok ctx
          Close -> not (continuing ctx) &&
                     checkTokenBurned tok ctx &&
                       not (checkTokenOut (fst (newDatum ctx)) ctx) &&
                         checkSigned (owner lab) ctx

checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx
  = case newDatumAddr addr ctx of
        (tok, l) -> ownAssetClass tn ctx == tok && checkRational (ratio l)

checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx
  = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

isInitial ::
          Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial addr oref tn ctx
  = consumes oref ctx &&
      checkDatum addr tn ctx && checkValue addr tn ctx

agdaPolicy ::
           Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial addr oref tn ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

