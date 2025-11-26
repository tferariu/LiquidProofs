module MWE' where

import Numeric.Natural (Natural)

data Datum = Holding
           | Collecting Natural Integer

validator :: Datum -> Natural -> ScriptContextt -> Bool
validator dat b ctx = getOtherr ctx == b

