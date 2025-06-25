module DEx where

data Label = Label{ratio :: Rational, owner :: PubKeyHash}

data Input = Update Value Rational
           | Exchange Integer PubKeyHash
           | Close

data Params = Params{sellC :: AssetClass, buyC :: AssetClass}

checkMinValue :: Value -> Bool
checkMinValue v = assetClassValueOf v ada >= 2

checkTokenIn :: AssetClass -> ScriptContext -> Bool
checkTokenIn tok ctx = assetClassValueOf (inputVal ctx) tok == 1

checkTokenOut :: AssetClass -> ScriptContext -> Bool
checkTokenOut tok ctx = assetClassValueOf (outputVal ctx) tok == 1

ratioCompare :: Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * num r <= b * den r

processPayment ::
               AssetClass -> Integer -> Rational -> Value -> Bool
processPayment ac amt r (MkMap []) = False
processPayment ac amt r (MkMap ((ac', amt') : vs))
  = if ac == ac' then ratioCompare amt amt' r else
      processPayment ac amt r (MkMap vs)

checkPayment :: Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l ctx
  = payTo ctx == owner l &&
      ratioCompare amt (assetClassValueOf (payVal ctx) (buyC par))
        (ratio l)
        && checkMinValue (payVal ctx)

checkBuyer ::
           Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx
  = buyTo ctx == pkh &&
      assetClassValueOf (buyVal ctx) (sellC par) == amt &&
        checkMinValue (buyVal ctx)

checkTokenBurned :: AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = mint ctx == (-1)

agdaValidator :: Params -> Datum -> Input -> ScriptContext -> Bool
agdaValidator par (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case red of
          Update v r -> checkSigned (owner lab) ctx &&
                          checkRational r &&
                            checkMinValue v &&
                              newValue ctx == v &&
                                newDatum ctx == (tok, Label r (owner lab)) &&
                                  continuing ctx && checkTokenOut tok ctx
          Exchange amt pkh -> oldValue ctx ==
                                newValue ctx <> assetClassValue (sellC par) amt
                                &&
                                newDatum ctx == (tok, lab) &&
                                  checkPayment par amt lab ctx &&
                                    checkBuyer par amt pkh ctx &&
                                      continuing ctx && checkTokenOut tok ctx
          Close -> not (continuing ctx) &&
                     checkTokenBurned tok ctx &&
                       not (checkTokenOut (fst (newDatum ctx)) ctx) &&
                         checkSigned (owner lab) ctx

consumes :: TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == inputRef ctx

checkDatum :: Address -> ScriptContext -> Bool
checkDatum addr ctx
  = case newDatum ctx of
        (tok, l) -> ownAssetClass ctx == tok && checkRational (ratio l)

checkValue :: Address -> ScriptContext -> Bool
checkValue addr ctx = checkTokenOut (ownAssetClass ctx) ctx

isInitial :: Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx
  = consumes oref ctx && checkDatum addr ctx && checkValue addr ctx

continuingAddr :: Address -> ScriptContext -> Bool
continuingAddr addr ctx = continues ctx

agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial addr oref ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

