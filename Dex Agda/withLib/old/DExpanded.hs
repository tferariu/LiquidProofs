module DExpanded where

data Label = Label{ratio :: Rational, owner :: PubKeyHash}

data Input = Update Integer Rational
           | Exchange Integer PubKeyHash
           | Close

data Params = Params{sellC :: AssetClass, buyC :: AssetClass}

checkPayment :: Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt st ctx
  = case getPaymentOutput (owner st) ctx of
        Nothing -> False
        Just tx -> ratioCompare amt (txOutValue tx) (ratio st)

checkBuyer ::
           Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx
  = case getPaymentOutput pkh ctx of
        Nothing -> False
        Just txO -> txOutValue txO == amt

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par st red ctx
  = case red of
        Update amt r -> checkSigned (owner st) ctx &&
                          checkRational r &&
                            newValue ctx == Just amt &&
                              newLabel ctx == Just (Label r (owner st)) && continuing ctx
        Exchange amt pkh -> oldValue ctx == maybe+ (newValue ctx) amt &&
                              newLabel ctx == Just st &&
                                checkPayment par amt st ctx &&
                                  checkBuyer par amt pkh ctx && continuing ctx
        Close -> not (continuing ctx) && checkSigned (owner st) ctx

