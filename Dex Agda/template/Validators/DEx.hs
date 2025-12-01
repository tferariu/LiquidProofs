module Validators.DEx where

import Lib (Address, AssetClass, PubKeyHash, Rational, TxOutRef, denominator, numerator)
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

checkDatum :: Address -> ScriptContext -> Bool
checkDatum addr ctx
  = case newDatumAddr addr ctx of
        (tok, l) -> ownAssetClass ctx == tok && checkRational (ratio l)

checkValue :: Address -> ScriptContext -> Bool
checkValue addr ctx
  = checkTokenOutAddr addr (ownAssetClass ctx) ctx

isInitial :: Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx
  = consumes oref ctx && checkDatum addr ctx && checkValue addr ctx

agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial addr oref ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

