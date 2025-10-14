module DExpanded2 where

data Label = Label{ratio :: Rational, owner :: PubKeyHash}

data Input = Update Integer Rational
           | Exchange Integer PubKeyHash
           | Close

data Params = Params{sellC :: AssetClass, buyC :: AssetClass}

checkPayment :: Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l ctx
  = any
      (\ txO ->
         txOutDatum txO == Payment (inputAddr ctx) &&
           processPayment (buyC par) amt (ratio l) (txOutValue txO))
      (getOutputsAtAddr (owner l) ctx)

