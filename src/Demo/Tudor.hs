{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.Tudor where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe
import           Data.Set                                   hiding (insert, delete)
import           Language.Haskell.Liquid.ProofCombinators

type PubKeyHash = String
type Value = Integer

data State = State { balances::(AccMap PubKeyHash Value), totalValue::Value}
{-@
data State = State
    { balances :: AccMap PubKeyHash Value
    , totalValue  :: {totalValue:Value | True  }
    }
@-}

--{-@ data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value @-}
data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

--{-@ data WDArgs = WDArgs PubKeyHash Value @-}
data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash


{-@ reflect delete @-}
delete :: Eq key => key -> AccMap key val -> AccMap key val
delete k1 Nil = Nil
delete k1 (Cons k0 v0 m)
    | k1 == k0 = m -- delete the current item
    | otherwise = Cons k0 v0 (delete k1 m) -- search to see if k1 is present

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
-- nub of UniqList = id compared to predicate

{-@ consMap
        ::   k:key
        ->   v:val
        -> AccMap {k':key | k /= k'} val
        -> AccMap key val
@-}
consMap :: key -> val -> AccMap key val -> AccMap key val
consMap k v m = Cons k v m

{-@ reflect insert @-}
insert :: Eq key => key -> val -> AccMap key val -> AccMap key val
insert k1 v1 Nil = Cons k1 v1 Nil
insert k1 v1 (Cons k0 v0 m)
    | k1 == k0 = Cons k1 v1 m -- replace the current item
    | otherwise = Cons k0 v0 (insert k1 v1 m) -- search to see if k1 is present

--correctness || could we do it factoring through the types
{-@ reflect lookup @-}
lookup :: Eq k => k -> AccMap k v -> Maybe v
lookup key Nil = Nothing
lookup key (Cons k v xs) 
    | key == k = Just v
    | otherwise = lookup key xs

--lookup would need induction
--{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: State -> AccountInput -> Maybe State @-}
openFunc :: State -> AccountInput -> Maybe State
openFunc (State accts currV) i = case i of
    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing -> 
            Just (State (insert pkh 0 accts) (currV)) 
    _ -> Nothing

{-@ reflect closeFunc @-}  
{-@ closeFunc :: State -> AccountInput -> Maybe State @-}                   
closeFunc :: State -> AccountInput -> Maybe State
closeFunc (State accts currV) i = case i of
    (Close pkh) -> case lookup pkh accts of
        Just 0 -> Just (State (delete pkh accts) (currV))
        _ -> Nothing
    _ -> Nothing


{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: State -> AccountInput -> Maybe State @-}                       
withdrawFunc :: State -> AccountInput -> Maybe State
withdrawFunc (State accts currV) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) && (v >= 0) then
            Just (State (insert pkh (v0 - v) accts) ((currV - v)))
                    else Nothing
    _ -> Nothing

{-@ reflect depositFunc @-}   
{-@ depositFunc :: State -> AccountInput -> Maybe State @-}                
depositFunc :: State -> AccountInput -> Maybe State
depositFunc (State accts currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if v >= 0 then
            Just (State (insert pkh (v0 + v) accts) (currV + v )) 
                    else Nothing
    _ -> Nothing 

--{-@ ple transferFunc@-}
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
                    (currV))
                else Nothing
    _ -> Nothing

{-@ measure getBalances @-}
getBalances :: State -> AccMap PubKeyHash Value
getBalances (State bal val) = bal


{-@ ple deletePreservesOthers@-}
{-@
deletePreservesOthers
    ::  pkh1:k
    ->   bal:AccMap k v
    -> {pkh2:k | pkh2 /= pkh1 }
    -> { lookup pkh2 bal == lookup pkh2 (delete pkh1 bal) }
@-}
deletePreservesOthers :: Eq k => k -> AccMap k v -> k -> Proof
deletePreservesOthers pkh1 Nil pkh2 = ()
deletePreservesOthers pkh1 (Cons pkh v m) pkh2 = deletePreservesOthers pkh1 m pkh2 
--could you get rid of this totally?


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
        Nothing -> insertPreservesOthers pkh1 0 accts pkh2
        Just v -> ()


{-@ ple closePreservesOthers@-}
{-@
closePreservesOthers
    ::   pkh1:PubKeyHash
    -> {   s0:State | (isJust (closeFunc s0 (Close pkh1))) }
    -> { pkh2:PubKeyHash | pkh2 /= pkh1 }
    -> { (lookup pkh2 (getBalances s0) == lookup pkh2 (getBalances (fromJust (closeFunc s0 (Close pkh1))))) }
@-}
closePreservesOthers :: PubKeyHash -> State -> PubKeyHash -> Proof
closePreservesOthers pkh1 s0@(State accts currV) pkh2 =
    case lookup pkh1 accts of
        Just 0 -> deletePreservesOthers pkh1 accts pkh2
        _ -> () 
        

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
withdrawPreservesOthers pkh1 val s0@(State accts currV) pkh2 =
    case lookup pkh1 accts of
        Nothing -> ()
        Just v0 
            | val <= v0 && val >= 0 -> insertPreservesOthers pkh1 (v0 - val) accts pkh2 
            | otherwise -> ()

--DO SOME ADDITIONAL AUTOMATION TO GET for free the lemmas
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
depositPreservesOthers pkh1 val s0@(State accts currV) pkh2 = 
    case lookup pkh1 accts of
        Nothing -> ()
        Just v0 
            | val >= 0 -> insertPreservesOthers pkh1 (v0 + val) accts pkh2 
            | otherwise -> ()


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
transferPreservesOthers pkh1 pkh2 v s0@(State accts currV) pkh3 =
    case lookup pkh1 accts of
        Nothing -> ()
        Just v1 -> case lookup pkh2 accts of
            Nothing -> ()
            Just v2 
                | (v <= v1) && (v >= 0) && (pkh1 /= pkh2) 
                    -> insertPreservesOthers pkh1 (v1 - v) (insert pkh2 (v2 + v) accts) pkh3 
                        ? insertPreservesOthers pkh2 (v2 + v) accts pkh3 
                | otherwise -> ()
--ask more questions

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

{-@ reflect transition @-}
{-@ transition :: State -> AccountInput -> Maybe State @-}
transition :: State -> AccountInput -> Maybe State
transition st i = case i of
    (Open _) -> openFunc st i
    (Close _) -> closeFunc st i               
    (Deposit _) -> depositFunc st i
    (Withdraw _) -> withdrawFunc st i
    (Transfer _) -> transferFunc st i

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
                                (currV)))
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
-}



{-
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
-}



{-
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
-}

{- 
() 
totalsLemma pkh val bal@(Cons k v m) tv 
    | pkh == k =    tv
                === sumVal bal
                === sumVal (Cons k val m)
                === val + sumVal m
                =>= val *** QED
    | otherwise = totalsLemma pkh val m (sumVal m)



-}



{-
       case lookup pkh1 accts of
            Nothing ->  True
                    === isJust (closeFunc s0 (Close pkh1))
                    === isJust Nothing
                    === False *** QED
            Just v 
                | v == 0 ->     
                    let (State bal _) = fromJust (closeFunc s0 (Close pkh1)) 
                    in
                    lookup pkh2 (getBalances (fromJust (closeFunc s0 (Close pkh1))))
                    === lookup pkh2 bal 
                    ==! lookup pkh2 (delete pkh1 accts) ? deletePreservesOthers pkh1 accts pkh2 
                    === lookup pkh2 accts             
                    === lookup pkh2 (getBalances s0) *** QED
--                    *** Admit
--                            === lookup pkh2 (getBalances (fromJust (Just (State (delete pkh1 accts) (currV `withProof` deleteZero pkh1 accts)))))
--                            === lookup pkh2 (getBalances (State (delete pkh1 accts) (currV `withProof` deleteZero pkh1 accts)))
                  --          === lookup pkh2 (getBalances ) 
                  --          === lookup pkh2 (delete pkh1 (let (State bal _) = fromJust (closeFunc s0 (Close pkh1)) in bal)) *** Admit
--                            === lookup pkh2 (delete pkh1 accts) ? deletePreservesOthers pkh1 accts pkh2 
--                            === lookup pkh2 accts             
--                            === lookup pkh2 (getBalances s0) *** QED
                | otherwise ->  True
                            === isJust (closeFunc s0 (Close pkh1))
                            === isJust Nothing
                            === False *** QED 
-}

{-
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
-}





{-
{-@ ple deletePreservesOthers@-}
{-@
deletePreservesOthers
    ::  pkh1:k
    ->   bal:AccMap k v
    -> {pkh2:k | pkh2 /= pkh1 }
    -> { lookup pkh2 bal == lookup pkh2 (delete pkh1 bal) }
@-}
deletePreservesOthers :: Eq k => k -> AccMap k v -> k -> Proof
deletePreservesOthers pkh1 bal@Nil pkh2 = ()
deletePreservesOthers pkh1 bal@(Cons pkh val m) pkh2 
                | pkh == pkh1 = () 
                | otherwise = deletePreservesOthers pkh1 m pkh2   

                    lookup pkh2 (delete pkh1 bal) 
                === lookup pkh2 (delete pkh1 [])
                === lookup pkh2 []
                === Nothing
                === lookup pkh2 (delete pkh1 bal) *** QED

     lookup pkh2 (delete pkh1 bal)
                             === lookup pkh2 (delete pkh1 ((pkh,v):xs))
                             === lookup pkh2 xs
                             === lookup pkh2 ((pkh,v):xs) *** QED

    lookup pkh2 (delete pkh1 bal)
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

{-
{-@                                          
type AscList val = [val]<{\v1 v2 -> v1 < v2}>
@-}                                          
                                             
{-@                                          
insert7 :: v:val -> l1:AscList val -> {l2:AscList val | True }
@-}                                          
insert7 :: Ord val => val -> [val] -> [val]  
insert7 v1 (v0 : asc)                        
    | v1 < v0   = v1 : v0 : asc              
    | otherwise = v0 : insert7 v1 asc        
insert7 v1 []   = v1 : []   

{-@ predicate Mem E L = member E (keys L) @-}
{-@ predicate Subset S L = (isSubsetOf (keys S) (keys L)) @-}

{-@ predicate DelSubset L2 L1 K = (Mem K L1 => (keys L1) == union (keys L2) (singleton K)) && (not (Mem K L1) => listElts L1 == listElts L2)@-}
{-@ predicate DelSubset2 L2 L1 K = (Mem K L1 => (listElts L1) == union (listElts L2) (singleton (K,specialVal L1 K))) && (not (Mem K L1) => listElts L1 == listElts L2)@-}

{-@ reflect specialVal @-}
{-@ specialVal::  l:[(_, _)] -> {k:_ | Mem k l} -> {e:_ | True} @-}
specialVal :: Eq a => [(a, b)] -> a -> b
specialVal accts pkh = case (lookup pkh accts `withProof` lem_lookMem pkh accts) of
  Just v  -> v




{-@ ple delete' @-}
{-@ reflect delete' @-}
{-@ delete' :: i:_ -> {l1:[(_, _)] | noDups l1} -> { l2:[(_, _)] | noDups l2 && DelSubset2 l2 l1 i && Subset l2 l1 && (not (Mem i l2))} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete' x xs

{-@ ple sumVal @-}
{-@ reflect sumVal @-}
{-@ sumVal :: Balances PubKeyHash Value -> Value @-}
sumVal :: Balances PubKeyHash Value -> Value
sumVal [] = 0
sumVal ((k,v):bs) = v + sumVal bs

{-@ ple insert2 @-}
{-@ reflect insert2 @-}
{-@ insert2 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value @-}
insert2 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value
insert2 key val [] = (key,val):[]
insert2 key val ((k,v):xs)
    | key == k = (key,val):xs
    | otherwise = (k,v):insert2 key val xs

{-@ ple insert3 @-}
{-@ reflect insert3 @-}
{-@ insert3 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value @-}
insert3 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value
insert3 key val bal = insert key val bal






{-@ measure sumAux @-}
{-@ sumAux :: [(String, Int)] -> Int @-}
sumAux :: [(String, Int)] -> Int
sumAux []       = 0
sumAux (x : xs) = (second x) + sumAux xs

{-@ measure second @-}
{-@ second:: (a,b) -> b @-}
second :: (a, b) -> b
second (a, b) = b

{-@ measure first @-}
{-@ first:: (a,b) -> a @-}
first :: (a, b) -> a
first (a, b) = a

{-@ reflect lookup' @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y) : xs) | x == x'   = Just y
                         | otherwise = lookup' x xs

--{-@ lookup' :: i:_ -> l:[(_, _)] -> {v0 : Maybe _ | ( isJust v0 ==> (Elem (i,(fromJust v0)) l) )} @-}
{-@ predicate Elem E L = (member E (listElts L)) @-}

{-@ reflect delete' @-}
--{-@ delete' :: i:_ -> [(_, _)] -> { l:[(_, _)] | not (Elem (i, (value i)) l)} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs) | x == x'   = xs
                         | otherwise = (x', y) : delete' x xs

{-@ reflect value @-}
value :: String -> [(String, Int)] -> Int
value k t = case lookup' k t of
  Just n  -> n
  Nothing -> 0

{-@ lem_delete :: k:_ -> t:_ ->  { sumAux (delete' k t) + (value k t) == sumAux t } @-}
lem_delete :: String -> [(String, Int)] -> ()
lem_delete x [] = ()
lem_delete x ((x', y) : xs) | x == x'   = ()
                            | otherwise = lem_delete x xs


{-@ lem_delOth :: k1:_ -> {k2:_ | k2 /= k1 } -> t:_ ->  { (value k1 t) = (value k1 (delete' k2 t)) } @-}
lem_delOth :: String -> String -> [(String, Int)] -> ()
lem_delOth a b [] = ()
lem_delOth a b ((x, y) : xs) | a == x   = ()
                             | b == x = lem_delOth a b xs
                             | otherwise = lem_delOth a b xs


--{-@ lem_deleteTwice :: g:_ -> {h:_ | g /= h } -> accts:_ -> { sumAux (delete' h (delete' g accts)) + (value g accts) + (value h (delete' g accts)) = sumAux accts } @-}
lem_deleteTwice :: String -> String -> [(String, Int)] -> ()
lem_deleteTwice x1 x2 [] = ()
lem_deleteTwice x1 x2 ((x, y) : xs) | x1 == x   = ()
                                    | x2 == x   = ()
                                    | otherwise = ()
                        
                        
{-@ type CorrectResult = {v:([(String, Int)],Int) | sumAux (first v) == second v}@-}

{-@ test :: _ -> pkh1:_ -> {pkh2:_ | True } -> accts :_ -> {currV:Int | sumAux accts == currV} -> Maybe CorrectResult @-}
test
  :: Int -> String -> String -> [(String, Int)] -> Int -> Maybe ([(String, Int)], Int)
test v pkh1 pkh2 accts currV = case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
  (Nothing,_) -> Nothing
  (_,Nothing) -> Nothing
  (Just v1,  Just v2) -> if (pkh1 == pkh2) then Nothing
    else Just ( (pkh2,v2+v):(((delete' pkh2 d1) `withProof` (lem_delete pkh2 d1)) `withProof` lem_delOth pkh2 pkh1 accts) , (currV))
    where
      d1 = (pkh1,v1-v) : (delete' pkh1 accts) `withProof` (lem_delete pkh1 accts)


{-@ lem_deleteTwice :: pkh1:_ -> {pkh2:_ | phk1 /= pkh2} -> accts:_ -> { sumAux (delete' pkh2 (delete' pkh1 accts)) + (value pkh1 accts) + (value pkh2 accts) = sumAux accts } @-}
lem_deleteTwice :: PubKeyHash -> PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_deleteTwice x1 x2 [] = ()
lem_deleteTwice x1 x2 ((x, y) : xs) | x1 == x   = lem_delete x2 xs
                                    | x2 == x   = lem_delete x1 xs
                                    | otherwise = lem_deleteTwice x1 x2 xs

      (-- (delete' pkh2  
        ((delete' pkh1 accts) `withProof` (lem_delete pkh1 accts))
      --  `withProof` (lem_delete pkh2 ((delete' pkh1 accts) `withProof` (lem_delete pkh1 accts))))
      , (currV - v1))
-}
-- https://nikivazou.github.io/static/popl18/refinement-reflection.pdf

{-@ reflect hasKey @-}
hasKey :: Eq k => k -> Balances k v -> Bool
hasKey _key          [] = False
hasKey  key ((k,_v):xs) = key == k || hasKey key xs

{-@ ple insert @-}
{-@ reflect insert @-}
{-@ insert :: _ -> _ -> b1:Balances _ _ -> {b2: Balances _ _ | keys b1 == keys b2} @-}
insert :: Eq k => k -> v -> Balances k v -> Balances k v
insert key val [] = []
insert key val ((k,v):xs)
    | key == k = (key,val):xs
    | otherwise = (k,v):insert key val xs

{-@ ple insert2 @-}
{-@ reflect insert2 @-}
--{-@ insert2 :: _ -> _ -> b1:Balances2 _ _ -> {b2: Balances2 _ _ | keys b1 == keys b2} @-}
insert2 :: Eq k => k -> v -> Balances k v -> Balances k v
--{-@ insert2 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value @-}
--insert2 :: PubKeyHash -> Value -> Balances PubKeyHash Value -> Balances PubKeyHash Value
insert2 key val [] = []
insert2 key val ((k,v):xs)
    | key == k = (key,val):xs
    | otherwise = (k,v):insert2 key val xs

--    -> {  b:k | a /= b }
{-@
insertPreservesUniqueness
    ::  pkh1:k
    ->  val1:v
    ->   bal:Balances k v
    -> {pkh2:k | pkh1 /= pkh2 }
    ->  val2:v   
    -> { True }
@-}
insertPreservesUniqueness :: Eq k => k -> v -> Balances k v -> k -> v -> Proof
insertPreservesUniqueness k1 v1 bal k2 v2 = () *** Admit

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-} 
{-@ insertt :: (Ord a) => a -> IncrList a -> IncrList a @-}
insertt y []     = [y]
insertt y (x:xs)
  | y <= x      = y : x : xs 
  | otherwise   = x : insertt y xs

{-@ reflect delete @-}
{-@ ple delete @-}
{-@ delete :: k:_ -> b1:Balances _ _ -> {b2: Balances _ _ | isSubsetOf (keys b2) (keys b1) && (not (member k (keys b2)))} @-}
delete :: Eq k => k -> Balances k v -> Balances k v
delete key [] = []
delete key ((k,v):xs)
    | key == k = xs
    | otherwise = (k,v):delete key xs

{-@ ple lem_lookMem @-}
{-@ lem_lookMem :: k:PubKeyHash -> AccMap  -> { ((lookup k l) == Nothing) <=> } @-}
--lem_lookMem :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_lookMem :: PubKeyHash -> AccMap PubKeyHash Value -> ()
lem_lookMem x [] = ()
lem_lookMem x ((x',y):xs) | x == x' = ()
                          | otherwise = lem_lookMem x xs

-}