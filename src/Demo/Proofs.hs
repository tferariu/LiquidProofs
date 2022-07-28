{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.Proofs where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe
import           Data.Set                                   hiding (insert, delete)
import           Language.Haskell.Liquid.ProofCombinators


type PubKeyHash = String
{-@ type Value = {v:Integer|v>=0} @-}
type Value = Integer

type Balances k v = [(k, v)]

{-@ foo:: State -> State @-}
foo :: State -> State
foo x = x

--second st == sumVal (first st)

{-
{-@ type State = {st:(Balances PubKeyHash Value, Value) | True} @-}
type State = (Balances PubKeyHash Value, Value)

{-@ data State = State (bal:: Balances<{\x -> x >= 0}>) {v:Value | sumVal bal == v} @-}
data State = State Balances Value 

{-@ data Balances <p :: Value -> Bool> = Balances (UniqList PubKeyHash Value<p>) @-}
data Balances = Balances [(PubKeyHash, Value)] --use data refinement instead
--maybe not use abstract refinements <>
-}


data State = State (Balances PubKeyHash Value) Value
{-@
data State = State
    { balances :: Balances PubKeyHash Value
    , totalValue  :: {totalValue:Value | sumVal balances == totalValue}
    }
@-}


{-@ measure second @-}
{-@ second:: (a,b) -> b @-}
second :: (a,b) -> b
second (a,b) = b

{-@ measure first @-}
{-@ first:: (a,b) -> a @-}
first :: (a,b) -> a
first (a,b) = a

{-@ reflect sumVal @-}
{-@ sumVal :: Balances PubKeyHash Value -> Value @-}
sumVal :: Balances PubKeyHash Value -> Value
sumVal [] = 0
sumVal ((k,v):bs) = v + sumVal bs

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

{-@ reflect lookup @-}
lookup :: Eq k => k -> Balances k v -> Maybe v
lookup key [] = Nothing
lookup key ((k,v):xs)
    | key == k = Just v
    | otherwise = lookup key xs

{-@ reflect hasKey @-}
hasKey :: Eq k => k -> Balances k v -> Bool
hasKey _key          [] = False
hasKey  key ((k,_v):xs) = key == k || hasKey key xs

{-@ reflect insert @-}
insert :: Eq k => k -> v -> Balances k v -> Balances k v
insert key val [] = (key,val):[]
insert key val ((k,v):xs)
    | key == k = (key,val):xs
    | otherwise = (k,v):insert key val xs

{-@ reflect delete @-}
delete :: Eq k => k -> Balances k v -> Balances k v
delete key [] = []
delete key ((k,v):xs)
    | key == k = xs
    | otherwise = (k,v):delete key xs

{-@
deletePreservesOthers
    ::  pkh1:k
    ->   bal:Balances k v
    -> {pkh2:k | pkh2 /= pkh1 }
    -> { lookup pkh2 bal == lookup pkh2 (delete pkh1 bal) }
@-}
deletePreservesOthers :: Eq k => k -> Balances k v -> k -> Proof
deletePreservesOthers pkh1 bal@[] pkh2 = 
                    lookup pkh2 (delete pkh1 bal) 
                === lookup pkh2 (delete pkh1 [])
                === lookup pkh2 []
                === Nothing
                === lookup pkh2 (delete pkh1 bal) *** QED
deletePreservesOthers pkh1 bal@((pkh,v):xs) pkh2
                | pkh == pkh1 =  lookup pkh2 (delete pkh1 bal)
                             === lookup pkh2 (delete pkh1 ((pkh,v):xs))
                             === lookup pkh2 xs
                             === lookup pkh2 ((pkh,v):xs) *** QED
                | otherwise =    lookup pkh2 (delete pkh1 bal)
                             === lookup pkh2 (delete pkh1 ((pkh,v):xs))
                             === lookup pkh2 ((pkh,v):(delete pkh1 xs)) ? lookupCases ((pkh,v):xs)
                             === lookup pkh2 ((pkh,v):xs)  *** Admit
    where
    lookupCases ((pkh,v):xs)
        | pkh == pkh2 = lookup pkh2 ((pkh,v):(delete pkh1 xs))
                    === Just v
                    === lookup pkh2 ((pkh,v):xs)
                    === lookup pkh2 bal *** QED
        | otherwise =   lookup pkh2 ((pkh,v):(delete pkh1 xs))
                    === lookup pkh2 (delete pkh1 xs) ? deletePreservesOthers pkh1 xs pkh2
                    === lookup pkh2 bal  *** QED

{-@
deleteRemovesVal
    ::   pkh:PubKeyHash
    ->   bal:Balances PubKeyHash Value
    -> { sumVal bal - (getValue pkh bal) == sumVal (delete pkh bal)}
@-}
deleteRemovesVal :: PubKeyHash -> Balances PubKeyHash Value -> Proof
deleteRemovesVal pkh bal =
    case lookup pkh bal of
        Nothing -> case bal of
            [] ->   sumVal (delete pkh [])
                === sumVal []
                === sumVal [] - 0
                === sumVal bal - (getValue pkh bal) *** QED
            ((k,v):bs)
                | k == pkh ->   True
                            === isJust (Just v)
                            === isJust (lookup pkh ((k,v):bs))
                            === isJust Nothing
                            === False *** QED
                | otherwise ->  sumVal (delete pkh bal)
                            === sumVal (delete pkh ((k,v):bs))
                            === sumVal ((k,v):(delete pkh bs)) 
                            === v + sumVal (delete pkh bs) ? deleteRemovesVal pkh bs
                            === v + sumVal bs - (getValue pkh bs) 
                            === sumVal ((k,v):bs) - (getValue pkh ((k,v):bs))  
                            === sumVal bal - (getValue pkh bal) *** QED
        Just v -> case bal of
            [] ->   sumVal (delete pkh [])
                === sumVal []
                === sumVal [] - 0
                === sumVal bal - (getValue pkh bal) *** QED
            ((k,v):bs)
                | k == pkh ->   sumVal (delete pkh bal)
                            === sumVal (delete pkh ((k,v):bs))
                            === sumVal bs
                            === sumVal bs + v - v
                            === sumVal ((k,v):bs) - (getValue pkh ((k,v):bs)) 
                            === sumVal bal - getValue pkh bal *** QED
                | otherwise ->  sumVal (delete pkh bal)
                            === sumVal (delete pkh ((k,v):bs))
                            === sumVal ((k,v):(delete pkh bs)) 
                            === v + sumVal (delete pkh bs) ? deleteRemovesVal pkh bs
                            === v + sumVal bs - (getValue pkh bs) 
                            === sumVal ((k,v):bs) - (getValue pkh ((k,v):bs))  
                            === sumVal bal - (getValue pkh bal) *** QED

{-@
insertPreservesOthers
    ::    a:k
    ->  val:v
    ->  xxs:Balances k v
    -> {  b:k | a /= b }
    -> { lookup b xxs == lookup b (insert a val xxs) }
@-}
insertPreservesOthers :: Eq k => k -> v -> Balances k v -> k -> Proof
insertPreservesOthers a val xxs b =
    let
    -- insertCases could be inlined as the body of insertPreservesOthers if you wanted
    insertCases =
      case xxs of
        [] ->
                lookup b (insert a val xxs) -- restate right side of conclusion
            === lookup b (insert a val [])  -- xxs == []
            === lookup b [(a, val)]      -- def of set
                -- lookup case for [] is excluded by `xxs==[(a,val)]`
                -- lookup case for `key==k` is excluded by premise `a/=b`
            === lookup b []  -- def of lookup
            === Nothing      -- def of lookup again
            === lookup b xxs -- obtain left side of conclusion (recall `xxs==[]`)
                -- WHY? `set` added `a` to empty-assoc `xxs`, but `a/=b` means
                -- `lookup b` was `Nothing` both before and after
            *** QED
        (k,v):xs
            | a == k ->
                    lookup b (insert a val xxs)        -- restate right side of conclusion
                === lookup b (insert a val ((a,v):xs)) -- xxs == (k,v):xs && a == k
                === lookup b ((a,val):xs)           -- def of set
                    -- lookup case for [] is excluded by `xxs=(a,val):xs`
                    -- lookup case for `key==k` is excluded by premise `a/=b`
                === lookup b xs  -- def of lookup
                === lookup b xxs -- obtain left side of conclusion
                    -- WHY? `set` replaced pair at head of `xxs`, but `a/=b`
                    -- means `lookup b` recurses past the head to the tail of
                    -- `xxs`, both before and after (congruency)
                *** QED
            | otherwise ->
                    lookup b (insert a val xxs)        -- restate right side of conclusion
                === lookup b (insert a val ((k,v):xs)) -- xxs == (k,v):xs
                === lookup b ((k,v):insert a val xs)   -- def of set && a /= k
                    -- lookup case for [] is excluded by `xxs=(k,v):xs`
                    ? lookupCases ((k,v):xs)
                *** QED
    -- lookupCases gets an inferred type that its arg is a nonempty list and `a /= k`
    lookupCases ((k,v):xs)
        | b == k =
                lookup b ((k,v):insert a val xs) -- restate evidince from callsite of lookupCases
            === Just v                        -- def of lookup && b == k
            === lookup b xxs                  -- obtain left side of conclusion
                -- WHY? `set` recurses past the head of `xxs` but `lookup`
                -- returns the value at the head
            *** QED
        | otherwise =
                lookup b ((k,v):insert a val xs) -- restate evidence from callsite of lookupCases
            === lookup b (insert a val xs)       -- def of lookup && b /= k
                ? insertPreservesOthers a val xs b -- apply induction hypothesis
            === lookup b xs                   -- left side of induction hypothesis
            === lookup b xxs                  -- obtain left side of conclusion
                -- WHY? `set` recurses past the head of `xxs` and so does
                -- `lookup`; we rely on the induction hypothesis and congruency
            *** QED
    in
    insertCases

{-@
insertModifiesByVal
    ::  pkh:PubKeyHash
    ->  val:Value
    ->  bal:Balances PubKeyHash Value
    -> { sumVal bal + val - (getValue pkh bal) == sumVal (insert pkh val bal)}
@-}
insertModifiesByVal :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Proof
insertModifiesByVal pkh val bal =
    case lookup pkh bal of
        Nothing -> case bal of
            [] ->   sumVal (insert pkh val [])
                === sumVal ((pkh, val):[])
                === sumVal [] + val
                === sumVal bal + val - 0 
                === sumVal bal + val - (getValue pkh bal) *** QED
            ((k,v):bs)
                | k == pkh ->   sumVal (insert pkh val ((k,v):bs))
                            === sumVal ((pkh, val):bs)
                            === val + sumVal bs 
                            === sumVal bal + val - 0 
                            === sumVal bal + val - (getValue pkh bal) *** QED
                | otherwise ->  sumVal (insert pkh val ((k,v):bs)) 
                            === sumVal ((k,v):insert pkh val bs)
                            === v + sumVal (insert pkh val bs) ? insertModifiesByVal pkh val bs
                            === v + sumVal bs + val - (getValue pkh bs)
                            === sumVal ((k, v):bs) + val - (getValue pkh bs)
                            === sumVal ((k, v):bs) + val - (getValue pkh bal) *** QED
        Just v -> case bal of
            [] ->   sumVal (insert pkh val [])
                === sumVal ((pkh, val):[])
                === val + sumVal []
                === val + sumVal bal *** QED
            ((k,v):bs)
                | k == pkh ->   sumVal (insert pkh val ((k,v):bs))
                            === sumVal ((pkh, val):bs)
                            === val + sumVal bs 
                            === val + sumVal bs + v - v 
                            === val + sumVal ((k,v):bs) - v
                            === sumVal ((k,v):bs) + val - getValue pkh ((k,v):bs) *** QED
                | otherwise ->  sumVal (insert pkh val ((k,v):bs)) 
                            === sumVal ((k,v):insert pkh val bs)
                            === v + sumVal (insert pkh val bs) ? insertModifiesByVal pkh val bs
                            === v + sumVal bs + val - (getValue pkh bs) 
                            === sumVal ((k, v):bs) + val - (getValue pkh bs)
                            === sumVal ((k, v):bs) + val - (getValue pkh bal) *** QED

{-@ measure getBalances @-}
getBalances :: State -> Balances PubKeyHash Value
getBalances (State bal val) = bal


{-@ reflect getValue @-}
getValue :: PubKeyHash -> Balances PubKeyHash Value -> Value
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
            Just (State (insert pkh 0 accts) (currV `withProof` insertModifiesByVal pkh 0 accts)) 
    _ -> Nothing

{-{-@
insertModifiesByVal
    ::  pkh:PubKeyHash
    ->  val:Value
    ->  bal:Balances PubKeyHash Value
    -> { sumVal bal + val - (getValue pkh bal) == sumVal (insert pkh val bal)}
@-}-}

{-@
insertZero
    ::   pkh:PubKeyHash
    -> { val:Value | val == 0 }
    -> { bal:Balances PubKeyHash Value | lookup pkh bal == Nothing }
    -> { sumVal bal == sumVal (insert pkh val bal)}
@-}
insertZero :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Proof
insertZero pkh val bal =    sumVal (insert pkh val bal) ? insertModifiesByVal pkh val bal
                        === sumVal bal + val - (getValue pkh bal) 
                        === sumVal bal + 0 - 0 
                        === sumVal bal *** QED

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
        Nothing ->  lookup pkh2 (getBalances (fromJust (openFunc s0 (Open pkh1)))) 
                === lookup pkh2 (getBalances (fromJust (Just (State (insert pkh1 0 accts) (currV `withProof` insertZero pkh1 0 accts))))) 
                === lookup pkh2 (getBalances (State (insert pkh1 0 accts) (currV `withProof` insertZero pkh1 0 accts)))
                === lookup pkh2 (insert pkh1 0 accts) ? insertPreservesOthers pkh1 0 accts pkh2 
                === lookup pkh2 accts               -- lookup b xxs == lookup b (insert a val xxs)
                === lookup pkh2 (getBalances s0) *** QED
        Just v ->   True
                === isJust (openFunc (State accts currV) (Open pkh1))
                === isJust Nothing
                === False *** QED


{-@
xxxxx
    ::    pkh:PubKeyHash
    -> {   s0:State | isJust (transition s0 (Open pkh)) }
    -> { isJust (openFunc s0 (Open pkh)) }
@-}
xxxxx :: PubKeyHash -> State -> Proof
xxxxx pkh s0 =  transition s0 (Open pkh) *** QED

--step in CBCAST
{-@ reflect transition @-}
{-@ transition :: State -> AccountInput -> Maybe State @-}
transition :: State -> AccountInput -> Maybe State
transition st i = case i of
    (Open _) -> openFunc st i
    (Close _) -> closeFunc st i               
    (Deposit _) -> depositFunc st i
    (Withdraw _) -> withdrawFunc st i
    (Transfer _) -> transferFunc st i



--{-@ ple closeFunc @-}
{-@ reflect closeFunc @-}  
{-@ closeFunc :: State -> AccountInput -> Maybe State @-}                   
closeFunc :: State -> AccountInput -> Maybe State
closeFunc (State accts currV) i = case i of
    (Close pkh) -> case lookup pkh accts `withProof` (getValue pkh accts) of
        Just 0 -> Just (State (delete pkh accts) (currV `withProof` deleteRemovesVal pkh accts))
        _ -> Nothing
    _ -> Nothing

{-
{-@ reflect getValue @-}
getValue :: PubKeyHash -> Balances PubKeyHash Value -> Value
getValue pkh bal = case lookup pkh bal of
  Just v  -> v
  Nothing -> 0
  {-@
deleteRemovesVal
    ::   pkh:PubKeyHash
    ->   bal:Balances PubKeyHash Value
    -> { sumVal bal - (getValue pkh bal) == sumVal (delete pkh bal)}
@-}-}

{-@
deleteZero
    ::   pkh:PubKeyHash
    -> { bal:Balances PubKeyHash Value | lookup pkh bal == Just 0 }
    -> { sumVal bal == sumVal (delete pkh bal)}
@-}
deleteZero :: PubKeyHash-> Balances PubKeyHash Value -> Proof
deleteZero pkh bal =    sumVal (delete pkh bal) ? deleteRemovesVal pkh bal
                        === sumVal bal- (getValue pkh bal) 
                        === sumVal bal - 0 
                        === sumVal bal *** QED

{-@ ple closePreservesOthers@-}
{-@
closePreservesOthers
    ::   pkh1:PubKeyHash
    -> {   s0:State | (isJust (closeFunc s0 (Close pkh1))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (closeFunc s0 (Close pkh1))))) }
@-}
closePreservesOthers :: PubKeyHash -> State -> PubKeyHash -> Proof
closePreservesOthers pkh1 s0@(State accts currV) pkh2
    | (isJust (closeFunc s0 (Close pkh1))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (closeFunc s0 (Close pkh1))
                    === isJust Nothing
                    === False *** QED
            Just v 
                | v == 0 ->     lookup pkh2 (getBalances (fromJust (closeFunc s0 (Close pkh1))))
                            === lookup pkh2 (getBalances (fromJust (Just (State (delete pkh1 accts) (currV `withProof` deleteZero pkh1 accts)))))
                            === lookup pkh2 (getBalances (State (delete pkh1 accts) (currV `withProof` deleteZero pkh1 accts)))
                            === lookup pkh2 (delete pkh1 accts) ? deletePreservesOthers pkh1 accts pkh2 
                            === lookup pkh2 accts               -- lookup b xxs == lookup b (close a val xxs)
                            === lookup pkh2 (getBalances s0) *** QED
                | otherwise ->  True
                            === isJust (closeFunc s0 (Close pkh1))
                            === isJust Nothing
                            === False *** QED
    | otherwise = () 


{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: State -> AccountInput -> Maybe State @-}                       
withdrawFunc :: State -> AccountInput -> Maybe State
withdrawFunc (State accts currV) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) && (v >= 0) then
            Just (State (insert pkh (v0 - v) accts) ((currV - v) 
                `withProof` insertMinusVal pkh v0 v accts `withProof` totalsLemma pkh v0 accts currV))
                    else Nothing
    _ -> Nothing

{-@ ple totalsLemma @-}
totalsLemma :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Value -> Proof
{-@
totalsLemma
    ::   pkh:PubKeyHash 
    ->   val:Value
    -> { bal:Balances PubKeyHash Value | lookup pkh bal == Just val}
    -> {  tv:Value | tv == sumVal bal }
    -> { val <= tv } 
@-}
totalsLemma pkh val bal tv = case bal of
    [] ->   True
        === isJust (lookup pkh [])
        === isJust Nothing
        === False *** QED
    ((k,v):bs)
        | k == pkh ->   tv
                    === sumVal bal
                    === sumVal ((k,val):bs)
                    === val + sumVal bs
                    =>= val *** QED
        | otherwise ->  tv
                    === sumVal ((k,v):bs)
                    === v + sumVal bs ? totalsLemma pkh val bs (sumVal bs)
                    =>= v + val 
                    =>= val *** QED

{-@
insertMinusVal
    ::   pkh:PubKeyHash
    ->    v0:Value
    -> { val:Value | v0 >= val }
    -> { bal:Balances PubKeyHash Value | lookup pkh bal == Just v0 }
    -> { sumVal bal - val == sumVal (insert pkh (v0 - val) bal)}
@-}
insertMinusVal :: PubKeyHash -> Value -> Value -> Balances PubKeyHash Value -> Proof
insertMinusVal pkh v0 val bal = sumVal (insert pkh (v0 - val) bal) ? insertModifiesByVal pkh (v0 - val) bal
                            === sumVal bal + (v0 - val) - (getValue pkh bal)
                            === sumVal bal + v0 - val - v0 
                            === sumVal bal - val *** QED

{-@ ple withdrawPreservesOthers@-}
{-@
withdrawPreservesOthers
    ::   pkh1:PubKeyHash
    ->    val:Integer
    -> {   s0:State | (isJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))))) }
@-}
withdrawPreservesOthers :: PubKeyHash -> Value -> State -> PubKeyHash -> Proof
withdrawPreservesOthers pkh1 val s0@(State accts currV) pkh2
    | (isJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))
                    === isJust Nothing
                    === False *** QED
            Just v0 
                | val <= v0 && val >= 0 ->  
                            lookup pkh2 (getBalances (fromJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))))
                            === lookup pkh2 (getBalances (fromJust (Just (State (insert pkh1 (v0 - val) accts) 
                                ((currV - val) `withProof` insertMinusVal pkh1 v0 val accts `withProof` totalsLemma pkh1 v0 accts currV)))))
                            === lookup pkh2 (getBalances (State (insert pkh1 (v0 - val) accts)
                                ((currV - val) `withProof` insertMinusVal pkh1 v0 val accts `withProof` totalsLemma pkh1 v0 accts currV)))
                            === lookup pkh2 (insert pkh1 (v0 - val) accts) 
                                ? insertPreservesOthers pkh1 (v0 - val) accts pkh2 
                            === lookup pkh2 accts             
                            === lookup pkh2 (getBalances s0) *** Admit
                | otherwise ->  True
                            === isJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = ()  


{-@ reflect depositFunc @-}   
{-@ depositFunc :: State -> AccountInput -> Maybe State @-}                
depositFunc :: State -> AccountInput -> Maybe State
depositFunc (State accts currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if v >= 0 then
            Just (State (insert pkh (v0 + v) accts) (currV + v `withProof` insertPlusVal pkh v0 v accts)) 
                    else Nothing
    _ -> Nothing 

{-@
insertPlusVal
    ::   pkh:PubKeyHash
    ->    v0:Value
    ->   val:Value  
    -> { bal:Balances PubKeyHash Value | lookup pkh bal == Just v0 }
    -> { sumVal bal + val == sumVal (insert pkh (v0 + val) bal)}
@-}
insertPlusVal :: PubKeyHash -> Value -> Value -> Balances PubKeyHash Value -> Proof
insertPlusVal pkh v0 val bal  = sumVal (insert pkh (v0 + val) bal) ? insertModifiesByVal pkh (v0 + val) bal
                            === sumVal bal + (v0 + val) - (getValue pkh bal)
                            === sumVal bal + v0 + val - v0 
                            === sumVal bal + val *** QED

{-@ ple depositPreservesOthers@-}
{-@
depositPreservesOthers
    ::   pkh1:PubKeyHash
    ->    val:Integer
    -> {   s0:State | (isJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))))) }
@-}
depositPreservesOthers :: PubKeyHash -> Value -> State -> PubKeyHash -> Proof
depositPreservesOthers pkh1 val s0@(State accts currV) pkh2
    | (isJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))
                    === isJust Nothing
                    === False *** QED
            Just v0 
                | val >= 0 ->   lookup pkh2 (getBalances (fromJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))))
                            === lookup pkh2 (getBalances (fromJust (Just (State (insert pkh1 (v0 + val) accts) 
                                (currV + val `withProof` insertPlusVal pkh1 v0 val accts)))))
                            === lookup pkh2 (getBalances (State (insert pkh1 (v0 + val) accts) 
                                (currV + val `withProof` insertPlusVal pkh1 v0 val accts)))
                            === lookup pkh2 (insert pkh1 (v0 + val) accts) 
                                ? insertPreservesOthers pkh1 (v0 + val) accts pkh2 
                            === lookup pkh2 accts               -- lookup b xxs == lookup b (close a val xxs)
                            === lookup pkh2 (getBalances s0) *** QED
                | otherwise ->  True
                            === isJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = () 

{-@ ple transferFunc@-}
{-@ reflect transferFunc @-}
{-@ transferFunc :: State -> AccountInput -> Maybe State @-}                     
transferFunc :: State -> AccountInput -> Maybe State
transferFunc (State accts currV) i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) -> case (lookup pkh1 accts) of
        Nothing -> Nothing
        Just v1 -> case (lookup pkh2 accts) of
            Nothing -> Nothing
            Just v2 -> 
                if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then
                    Just (State (insert pkh1 (v1 - v) (insert pkh2 (v2 + v) accts)) 
                    (currV `withProof` insertMinusVal pkh1 v1 v (insert pkh2 (v2 + v) accts
                    `withProof` doubleInsert pkh1 v1 pkh2 (v2 + v) accts) 
                    `withProof` insertPlusVal pkh2 v2 v accts))
                else Nothing
    _ -> Nothing



{-@ ple doubleInsert@-}
doubleInsert :: PubKeyHash -> Value -> PubKeyHash -> Value -> Balances PubKeyHash Value -> Proof
{-@
doubleInsert
    ::  pkh1:PubKeyHash
    ->    v1:Value
    -> {pkh2:PubKeyHash | pkh1 /= pkh2 }
    ->    v2:Value  
    -> { bal:Balances PubKeyHash Value | lookup pkh1 bal == Just v1 }
    -> { lookup pkh1 (insert pkh2 v2 bal) == Just v1 }
@-}
doubleInsert pkh1 v1 pkh2 v2 bal = case bal of
    [] ->   True
        === isJust (lookup pkh1 bal)
        === isJust (lookup pkh1 [])
        === isJust Nothing
        === False *** QED
    ((k,v):bs) 
        | k == pkh2 ->  lookup pkh1 (insert pkh2 v2 bal)
                    === lookup pkh1 (insert pkh2 v2 ((k,v):bs)) 
                    === lookup pkh1 ((k,v2):bs)
                    === lookup pkh1 bs
                    === lookup pkh1 ((k,v):bs)
                    === Just v1 *** QED
        | k == pkh1 && v /= v1 ->   True
                                === v /= v1
                                === v /= fromJust (Just v1)
                                === v /= fromJust (lookup pkh1 ((k,v):bs))
                                === v /= fromJust (Just v)
                                === v /= v
                                === False *** QED
        | k == pkh1 && v == v1 ->  
                        lookup pkh1 (insert pkh2 v2 bal)
                    === lookup pkh1 (insert pkh2 v2 ((k,v):bs))
                    === lookup pkh1 ((k,v):(insert pkh2 v2 bs))
                    === Just v
                    === Just v1 *** QED
        | otherwise ->  lookup pkh1 (insert pkh2 v2 bal)
                    === lookup pkh1 (insert pkh2 v2 ((k,v):bs))
                    === lookup pkh1 ((k,v):(insert pkh2 v2 bs))
                    === lookup pkh1 (insert pkh2 v2 bs) ? doubleInsert pkh1 v1 pkh2 v2 bs
                    === Just v1 *** QED


{-@ ple transferPreservesOthers@-}
{-@
transferPreservesOthers
    ::   pkh1:PubKeyHash
    ->   pkh2:PubKeyHash
    ->      v:Integer
    -> {   s0:State | (isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))) }
    -> { pkh3:PubKeyHash | pkh3 /= pkh2 && pkh3 /= pkh1 }
    -> { (lookup pkh3 (getBalances s0) == lookup pkh3 (getBalances (fromJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))))) }
@-}
transferPreservesOthers :: PubKeyHash -> PubKeyHash -> Value -> State -> PubKeyHash -> Proof
transferPreservesOthers pkh1 pkh2 v s0@(State accts currV) pkh3
    | (isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))
                    === isJust Nothing
                    === False *** QED
            Just v1 -> case lookup pkh2 accts of
                Nothing ->  True
                        === isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))
                        === isJust Nothing
                        === False *** QED
                Just v2 
                    | (v <= v1) && (v >= 0) && (pkh1 /= pkh2) ->   
                                lookup pkh3 (getBalances (fromJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))))
                            === lookup pkh3 (getBalances (fromJust (Just (State (insert pkh1 (v1 - v) (insert pkh2 (v2 + v) accts)) 
                                (currV `withProof` insertMinusVal pkh1 v1 v (insert pkh2 (v2 + v) accts
                                `withProof` doubleInsert pkh1 v1 pkh2 (v2 + v) accts) 
                                `withProof` insertPlusVal pkh2 v2 v accts)))))
                            === lookup pkh3 (getBalances (State (insert pkh1 (v1 - v) (insert pkh2 (v2 + v) accts))
                                (currV `withProof` insertMinusVal pkh1 v1 v (insert pkh2 (v2 + v) accts
                                `withProof` doubleInsert pkh1 v1 pkh2 (v2 + v) accts) 
                                `withProof` insertPlusVal pkh2 v2 v accts)))
                            === lookup pkh3 (insert pkh1 (v1 - v) (insert pkh2 (v2 + v) accts))
                                ? insertPreservesOthers pkh1 (v1 - v) (insert pkh2 (v2 + v) accts) pkh3 
                            === lookup pkh3 (insert pkh2 (v2 + v) accts) 
                                ? insertPreservesOthers pkh2 (v2 + v) accts pkh3
                            === lookup pkh3 accts            
                            === lookup pkh3 (getBalances s0) *** QED
                    | otherwise -> True
                            === isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 v)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = ()



{-@ measure getPkh @-}
getPkh :: AccountInput -> PubKeyHash
getPkh (Open pkh) = pkh
getPkh (Close pkh) = pkh
getPkh (Deposit (WDArgs pkh v)) = pkh
getPkh (Withdraw (WDArgs pkh v)) = pkh
getPkh (Transfer (TransferArgs pkh1 pkh2 v)) = pkh1

{-@ measure getPkh2 @-}
getPkh2 :: AccountInput -> PubKeyHash
getPkh2 (Open pkh) = pkh
getPkh2 (Close pkh) = pkh
getPkh2 (Deposit (WDArgs pkh v)) = pkh
getPkh2 (Withdraw (WDArgs pkh v)) = pkh
getPkh2 (Transfer (TransferArgs pkh1 pkh2 v)) = pkh2

{-@
transitionPreservesOthers
    ::   s0:State
    -> {  i:AccountInput | (isJust (transition s0 i)) }
    -> {  k:PubKeyHash | k /= (getPkh i) && k /= (getPkh2 i)}
    -> { (lookup k (getBalances s0) == lookup k (getBalances (fromJust (transition s0 i)))) }
@-}
transitionPreservesOthers :: State -> AccountInput -> PubKeyHash -> Proof
transitionPreservesOthers st0 i k =
    let st = (st0 ? transition st0 i) in
        case i of
            (Open pkh) -> openPreservesOthers pkh st k  *** QED           
            (Close pkh) -> closePreservesOthers pkh st k *** QED
            (Deposit (WDArgs pkh v)) -> depositPreservesOthers pkh v st k *** QED
            (Withdraw (WDArgs pkh v)) -> withdrawPreservesOthers pkh v st k *** QED
            (Transfer (TransferArgs pkh1 pkh2 v)) -> transferPreservesOthers pkh1 pkh2 v st k *** QED



{-

{-@ measure getPkh @-}
getPkh :: AccountInput -> [PubKeyHash]
getPkh (Open pkh) = [pkh]
getPkh (Close pkh) = [pkh]
getPkh (Deposit (WDArgs pkh v)) = [pkh]
getPkh (Withdraw (WDArgs pkh v)) = [pkh]
getPkh (Transfer (TransferArgs pkh1 pkh2 v)) = (pkh1:[pkh2])

{-@ inline notChanging @-}
{-@ notChanging :: pkhs:[PubKeyHash] -> PubKeyHash -> Bool / [len pkhs]  @-}
notChanging :: [PubKeyHash] -> PubKeyHash -> Bool
notChanging [] k = True
notChanging (pkh:pkhs) k = k /= pkh && (notChanging pkhs k)

-}




