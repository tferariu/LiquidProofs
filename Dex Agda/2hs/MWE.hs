module MWE where

import Numeric.Natural (Natural)
import qualified Test (Bar, Foo, FooBar, ScriptContext, newDatum, newValue, oldValue)

getFoo ::
       Test.Foo Integer -> Test.Bar Integer -> Test.FooBar Integer
getFoo a b = a + b

foo :: Natural -> Test.ScriptContext Integer -> Bool
foo n ctx = Test.newValue ctx == n

validator ::
          Test.Foo Integer -> Integer -> Test.ScriptContext Integer -> Bool
validator f b ctx
  = Test.newValue ctx == Test.oldValue ctx && Test.newDatum ctx == b

