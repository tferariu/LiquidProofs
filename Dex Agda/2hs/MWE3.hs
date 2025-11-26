module MWE3 where

import qualified MWE2 (FOObar, FooBar(asdf1))
import Numeric.Natural (Natural)

foobar :: MWE2.FOObar Natural -> Natural
foobar x = MWE2.asdf1 x

