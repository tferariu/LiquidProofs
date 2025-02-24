{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.HangsEndlessly where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe
import           Data.Set                                   hiding (insert, delete)
import           Language.Haskell.Liquid.ProofCombinators


type PubKeyHash = String
{-@ type Value = {v:Integer|v>=0} @-}
type Value = Integer

data AccMap key val
    = Cons key val (AccMap key val)
    | Nil
{-@
data AccMap key val
    = Cons
        { mapKey :: key
        , mapVal :: val
        , mapTl  :: AccMap {kt:key | mapKey /= kt} val
        }
    | Nil
@-}

{-@ reflect lookup @-}
lookup :: Eq k => k -> AccMap k v -> Maybe v
lookup key Nil = Nothing
lookup key (Cons k v xs) 
    | key == k = Just v
    | otherwise = lookup key xs


{-@ reflect insert @-}
insert :: Eq key => key -> val -> AccMap key val -> AccMap key val
insert k1 v1 Nil = Cons k1 v1 Nil
insert k1 v1 (Cons k0 v0 m)
    | k1 == k0 = Cons k1 v1 m
    | otherwise = Cons k0 v0 (insert k1 v1 m)


data State = State (AccMap PubKeyHash Value) Value
{-@
data State = State
    { accts :: AccMap PubKeyHash Value
    , totalValue  :: {totalValue:Value | sumVal accts == totalValue}
    }
@-}

{-@ reflect sumVal @-}
{-@ sumVal :: AccMap PubKeyHash Value -> Value @-}
sumVal :: AccMap PubKeyHash Value -> Value
sumVal Nil = 0
sumVal (Cons k v bs) = v + sumVal bs

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

{-@ ple insertPreservesOthers @-}
{-@
insertPreservesOthers
    :: pkh1:k
    ->  val:v
    ->  xxs:AccMap k v
    ->{pkh2:k | pkh1 /= pkh2 }
    -> { lookup pkh2 xxs == lookup pkh2 (insert pkh1 val xxs) }
@-}
insertPreservesOthers :: Eq k => k -> v -> AccMap k v -> k -> Proof
insertPreservesOthers pkh1 val Nil pkh2 = ()
insertPreservesOthers pkh1 val (Cons pkh v m) pkh2 = insertPreservesOthers pkh1 val m pkh2 

{-@ ple insertModifiesByVal@-}
{-@
insertModifiesByVal
    ::  pkh:PubKeyHash
    ->  val:Value
    ->  bal:AccMap PubKeyHash Value
    -> { sumVal bal + val - (getValue pkh bal) == sumVal (insert pkh val bal)}
@-}
insertModifiesByVal :: PubKeyHash -> Value -> AccMap PubKeyHash Value -> Proof
insertModifiesByVal pkh val Nil = ()
insertModifiesByVal pkh val (Cons k v m) = insertModifiesByVal pkh val m

{-@ measure getBalances @-}
getBalances :: State -> AccMap PubKeyHash Value
getBalances (State bal val) = bal

{-@ reflect getValue @-}
getValue :: PubKeyHash -> AccMap PubKeyHash Value -> Value
getValue pkh bal = case lookup pkh bal of
  Just v  -> v
  Nothing -> 0

{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: State -> AccountInput -> Maybe State @-}
openFunc :: State -> AccountInput -> Maybe State
openFunc (State accts currV) i = case i of
    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing -> 
            Just (State (insert pkh 0 accts) 
            (currV `withProof` insertModifiesByVal pkh 0 accts)) 
    _ -> Nothing

{-@ ple openPreservesOthers@-}
{-@
openPreservesOthers
    ::   pkh1:PubKeyHash
    -> {   s0:State | isJust (openFunc s0 (Open pkh1)) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (openFunc s0 (Open pkh1)))) }
@-}
openPreservesOthers :: PubKeyHash -> State -> PubKeyHash -> Proof
openPreservesOthers pkh1 s0@(State accts currV) pkh2 = 
    case lookup pkh1 accts of
        Nothing -> insertPreservesOthers pkh1 0 accts pkh2 *** QED
        Just v ->   True
                === isJust (openFunc (State accts currV) (Open pkh1))
                === isJust (case lookup pkh1 accts of
                                Just _  -> Nothing 
                                Nothing -> Just (State (insert pkh1 0 accts) 
                                    (currV `withProof` insertModifiesByVal pkh1 0 accts)))
                === isJust Nothing
                === False *** QED

