module Validators.Template where

import Lib (Address, AssetClass, TxOutRef)

type Info = Placeholder

type Label = (AssetClass, Info)

data Input = Placeholder'

data Params = Params{optional :: Placeholder}

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx = True

agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx = True

