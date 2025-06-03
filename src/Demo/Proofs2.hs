{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}
--- CORRECTNESS PROOFS!!
--certora merkle trees?
module Demo.Proofs2 where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe
import           Data.Set                                   hiding (insert, delete)
import           Language.Haskell.Liquid.ProofCombinators


type PubKeyHash = String
{-@ type Value = {v:Integer|v>=0} @-}
type Value = Integer

type Balances k v = [(k, v)]

--data Bla = Bla [(a,b)]

{-@ foo:: State -> State @-}
foo :: State -> State
foo x = x

--{-@ type State = (Balances PubKeyHash Value, Value)<{\x y -> sumval x == y}> @-}
type State = (Balances PubKeyHash Value, Value)

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

--{-@ inline AccountInput @-}
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
                === lookup pkh2 [] *** QED
deletePreservesOthers pkh1 bal@((pkh,v):xs) pkh2
                | pkh == pkh1 =  lookup pkh2 (delete pkh1 bal)
                             === lookup pkh2 (delete pkh1 ((pkh,v):xs))
                             === lookup pkh2 xs
                             === lookup pkh2 ((pkh,v):xs) *** QED
                | otherwise =    lookup pkh2 (delete pkh1 bal)
                             === lookup pkh2 (delete pkh1 ((pkh,v):xs))
                             === lookup pkh2 ((pkh,v):(delete pkh1 xs)) ? lookupCases ((pkh,v):xs)
                             === lookup pkh2 ((pkh,v):xs)  *** QED
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

{-
{-@ reflect openAcc @-}
--{-@ openAcc :: st1:State -> i:AccountInput -> {st2:Maybe State | True}@-}
openAcc :: Balances PubKeyHash Value -> PubKeyHash -> Balances PubKeyHash Value
openAcc accts key = case lookup pkh accts of
    Just _  -> Nothing 
    Nothing ->
            Just ((insert pkh 0 accts), currV)
-}

{-@ reflect openFunc @-}
openFunc :: State -> AccountInput -> Maybe State
openFunc (accts, currV) i = case i of
    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just ((insert pkh 0 accts), currV)
    _ -> Nothing

{-@ inline getBalances @-}
getBalances :: State -> Balances PubKeyHash Value
getBalances (bal, _) = bal

{-@
openPreservesOthers
    ::   pkh1:PubKeyHash
    -> {   s0:State | isJust (openFunc s0 (Open pkh1)) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (openFunc s0 (Open pkh1)))) }
@-}
openPreservesOthers :: PubKeyHash -> State -> PubKeyHash -> Proof
openPreservesOthers pkh1 (accts, currV) pkh2 =
    case lookup pkh1 accts of
        Nothing ->  lookup pkh2 (getBalances (fromJust (openFunc (accts, currV) (Open pkh1))))
                === lookup pkh2 (getBalances (fromJust (Just ((insert pkh1 0 accts), currV))))
                === lookup pkh2 (getBalances ((insert pkh1 0 accts), currV))
                === lookup pkh2 (insert pkh1 0 accts) ? insertPreservesOthers pkh1 0 accts pkh2 
                === lookup pkh2 accts               -- lookup b xxs == lookup b (insert a val xxs)
                === lookup pkh2 (getBalances (accts, currV)) *** QED
        Just v ->   True
                === isJust (openFunc (accts, currV) (Open pkh1))
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


{-@ reflect closeFunc @-}                     
closeFunc :: State -> AccountInput -> Maybe State
closeFunc (accts, currV) i = case i of
    (Close pkh) -> case lookup pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just ((delete pkh accts), currV)
                        else Nothing
    _ -> Nothing

{-@
closePreservesOthers
    ::   pkh1:PubKeyHash
    -> {   s0:State | (isJust (closeFunc s0 (Close pkh1))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (closeFunc s0 (Close pkh1))))) }
@-}
closePreservesOthers :: PubKeyHash -> State -> PubKeyHash -> Proof
closePreservesOthers pkh1 (accts, currV) pkh2
    | (isJust (closeFunc (accts, currV) (Close pkh1))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (closeFunc (accts, currV) (Close pkh1))
                    === isJust Nothing
                    === False *** QED
            Just v 
                | v == 0 ->     lookup pkh2 (getBalances (fromJust (closeFunc (accts, currV) (Close pkh1))))
                            === lookup pkh2 (getBalances (fromJust (Just ((delete pkh1 accts), currV))))
                            === lookup pkh2 (getBalances ((delete pkh1 accts), currV))
                            === lookup pkh2 (delete pkh1 accts) ? deletePreservesOthers pkh1 accts pkh2 
                            === lookup pkh2 accts               -- lookup b xxs == lookup b (close a val xxs)
                            === lookup pkh2 (getBalances (accts, currV)) *** QED
                | otherwise ->  True
                            === isJust (closeFunc (accts, currV) (Close pkh1))
                            === isJust Nothing
                            === False *** QED
    | otherwise = () 


{-@ reflect withdrawFunc @-}                      
withdrawFunc :: State -> AccountInput -> Maybe State
withdrawFunc (accts, currV) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) then
            Just ((insert pkh (v0 - v) accts), (currV - v))
                    else Nothing
    _ -> Nothing

{-@
withdrawPreservesOthers
    ::   pkh1:PubKeyHash
    ->    val:Integer
    -> {   s0:State | (isJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (withdrawFunc s0 (Withdraw (WDArgs pkh1 val)))))) }
@-}
withdrawPreservesOthers :: PubKeyHash -> Value -> State -> PubKeyHash -> Proof
withdrawPreservesOthers pkh1 val (accts, currV) pkh2
    | (isJust (withdrawFunc (accts, currV) (Withdraw (WDArgs pkh1 val)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (withdrawFunc (accts, currV) (Withdraw (WDArgs pkh1 val)))
                    === isJust Nothing
                    === False *** QED
            Just v0 
                | val <= v0 ->  lookup pkh2 (getBalances (fromJust (withdrawFunc (accts, currV) (Withdraw (WDArgs pkh1 val)))))
                            === lookup pkh2 (getBalances (fromJust (Just ((insert pkh1 (v0 - val) accts), (currV - val)))))
                            === lookup pkh2 (getBalances ((insert pkh1 (v0 - val) accts), (currV - val)))
                            === lookup pkh2 (insert pkh1 (v0 - val) accts) 
                                ? insertPreservesOthers pkh1 (v0 - val) accts pkh2 
                            === lookup pkh2 accts               -- lookup b xxs == lookup b (close a val xxs)
                            === lookup pkh2 (getBalances (accts, currV)) *** QED
                | otherwise ->  True
                            === isJust (withdrawFunc (accts, currV) (Withdraw (WDArgs pkh1 val)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = ()  


{-@ reflect depositFunc @-}                   
depositFunc :: State -> AccountInput -> Maybe State
depositFunc (accts, currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if v >= 0 then
            Just ((insert pkh (v0 + v) accts), (currV + v))
                    else Nothing
    _ -> Nothing

{-@
depositPreservesOthers
    ::   pkh1:PubKeyHash
    ->    val:Integer
    -> {   s0:State | (isJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (depositFunc s0 (Deposit (WDArgs pkh1 val)))))) }
@-}
depositPreservesOthers :: PubKeyHash -> Value -> State -> PubKeyHash -> Proof
depositPreservesOthers pkh1 val (accts, currV) pkh2
    | (isJust (depositFunc (accts, currV) (Deposit (WDArgs pkh1 val)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (depositFunc (accts, currV) (Deposit (WDArgs pkh1 val)))
                    === isJust Nothing
                    === False *** QED
            Just v0 
                | val >= 0 ->   lookup pkh2 (getBalances (fromJust (depositFunc (accts, currV) (Deposit (WDArgs pkh1 val)))))
                            === lookup pkh2 (getBalances (fromJust (Just ((insert pkh1 (v0 + val) accts), (currV + val)))))
                            === lookup pkh2 (getBalances ((insert pkh1 (v0 + val) accts), (currV + val)))
                            === lookup pkh2 (insert pkh1 (v0 + val) accts) 
                                ? insertPreservesOthers pkh1 (v0 + val) accts pkh2 
                            === lookup pkh2 accts               -- lookup b xxs == lookup b (close a val xxs)
                            === lookup pkh2 (getBalances (accts, currV)) *** QED
                | otherwise ->  True
                            === isJust (depositFunc (accts, currV) (Deposit (WDArgs pkh1 val)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = () 

{-@ reflect transferFunc @-}    
--{-@ stuff @-}                 
transferFunc :: State -> AccountInput -> Maybe State
transferFunc  (accts, currV) i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) -> case (lookup pkh1 accts) of
        Nothing -> Nothing
        Just v1 -> case (lookup pkh2 accts) of
            Nothing -> Nothing
            Just v2 -> if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then
                Just ((insert pkh1 (v1 - v) (insert pkh2 (v2 + v) accts)), currV)
                        else Nothing
    _ -> Nothing

-- preconditions for transfer
{-@
transferPreservesOthers
    ::   pkh1:PubKeyHash
    ->   pkh2:PubKeyHash
    ->    val:Integer
    -> {   s0:State | (isJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 val)))) } 
    -> { pkh3:PubKeyHash | pkh3 /= pkh2 && pkh3 /= pkh1 }
    -> { (lookup pkh3 (getBalances s0) == 
            lookup pkh3 (getBalances (fromJust (transferFunc s0 (Transfer (TransferArgs pkh1 pkh2 val)))))) }
@-}
transferPreservesOthers :: PubKeyHash -> PubKeyHash -> Value -> State -> PubKeyHash -> Proof
transferPreservesOthers pkh1 pkh2 val (accts, currV) pkh3
    | (isJust (transferFunc (accts, currV) (Transfer (TransferArgs pkh1 pkh2 val)))) =
        case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (transferFunc (accts, currV) (Transfer (TransferArgs pkh1 pkh2 val)))
                    === isJust Nothing
                    === False *** QED
            Just v1 -> case lookup pkh2 accts of
                Nothing ->  True
                        === isJust (transferFunc (accts, currV) (Transfer (TransferArgs pkh1 pkh2 val)))
                        === isJust Nothing
                        === False *** QED
                Just v2 
                    | (val <= v1) && (val >= 0) && (pkh1 /= pkh2) ->   
                                lookup pkh3 (getBalances (fromJust (transferFunc (accts, currV) (Transfer (TransferArgs pkh1 pkh2 val)))))
                            === lookup pkh3 (getBalances (fromJust (Just ((insert pkh1 (v1 - val) (insert pkh2 (v2 + val) accts)), currV))))
                            === lookup pkh3 (getBalances ((insert pkh1 (v1 - val) (insert pkh2 (v2 + val) accts)), currV))
                            === lookup pkh3 (insert pkh1 (v1 - val) (insert pkh2 (v2 + val) accts))
                                ? insertPreservesOthers pkh1 (v1 - val) (insert pkh2 (v2 + val) accts) pkh3 
                            === lookup pkh3 (insert pkh2 (v2 + val) accts) 
                                ? insertPreservesOthers pkh2 (v2 + val) accts pkh3
                            === lookup pkh3 accts            
                            === lookup pkh3 (getBalances (accts, currV)) *** QED
                    | otherwise ->  True
                            === isJust (transferFunc (accts, currV) (Transfer (TransferArgs pkh1 pkh2 val)))
                            === isJust Nothing
                            === False *** QED
    | otherwise = ()


    
--    _ -> Nothing -- todo



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
transitionPreservesOthers (accts, currV) i k =
    let st = ((accts, currV) ? transition (accts, currV) i) in
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


