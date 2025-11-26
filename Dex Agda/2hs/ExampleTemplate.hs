module ExampleTemplate where

data Datum = Holding
           | Collecting Value PubKeyHash Integer [PubKeyHash]

data Input = Propose Value PubKeyHash Integer
           | Add PubKeyHash
           | Pay
           | Cancel
           | Close

validator :: Datum -> Input -> ScriptContext -> Bool
validator d i ctx = newValue ctx == oldValue ctx

