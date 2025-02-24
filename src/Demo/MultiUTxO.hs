{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.MultiUTxO where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe
import           Data.Set                                   hiding (insert, delete)
import           Language.Haskell.Liquid.ProofCombinators


type PubKeyHash = String
--change the spec !!!!!!!!!!!

--justify the specifation changes and such (frame or counterexample)
type ThreadTokenHash = String
{-@ type Value2 = {v:Integer|v>=0} @-}
type Value = Integer

--ghostVariable / refinement
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

{-@ reflect delete @-}
delete :: Eq key => key -> AccMap key val -> AccMap key val
delete k1 Nil = Nil
delete k1 (Cons k0 v0 m)
    | k1 == k0 = m -- delete the current item
    | otherwise = Cons k0 v0 (delete k1 m) -- search to see if k1 is present

{-@ reflect insert @-}
insert :: Eq key => key -> val -> AccMap key val -> AccMap key val
insert k1 v1 Nil = Cons k1 v1 Nil
insert k1 v1 (Cons k0 v0 m)
    | k1 == k0 = Cons k1 v1 m -- replace the current item
    | otherwise = Cons k0 v0 (insert k1 v1 m) -- search to see if k1 is present

--- actual code VS code relating to the spec
--story (e.g abstraction and refinement)

data Environment = Environment (AccMap ThreadTokenHash State)
{-@
data Environment = Environment
    { accts :: AccMap ThreadTokenHash State
    }
@-}

{-@ measure getAccounts @-}
getAccounts :: Environment -> AccMap ThreadTokenHash State
getAccounts (Environment accts) = accts

data State = State PubKeyHash Value
{-@
data State = State
    { pkh :: PubKeyHash
    , val :: Value2
    }
@-}



--data TransferArgs = TransferArgs PubKeyHash ThreadTokenHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer WDArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

data EnvironmentInput = EnvironmentInput ThreadTokenHash ThreadTokenHash AccountInput
                 





{-@ ple insertPreservesOthers @-}
{-@
insertPreservesOthers
    ::   k1:k
    ->  val:v
    ->  map:AccMap k v
    ->{  k2:k | k1 /= k2 }
    -> { lookup k2 map == lookup k2 (insert k1 val map) }
@-}
insertPreservesOthers :: Eq k => k -> v -> AccMap k v -> k -> Proof
insertPreservesOthers pkh1 val Nil pkh2 = ()
insertPreservesOthers pkh1 val (Cons pkh v m) pkh2 = insertPreservesOthers pkh1 val m pkh2 

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


--authenticate and signatories??

{-@ reflect withdrawSM @-}
{-@ withdrawSM :: State -> AccountInput -> Maybe State @-}                       
withdrawSM :: State -> AccountInput -> Maybe State
withdrawSM (State pkh val) i = case i of
    (Withdraw (WDArgs pkh v)) -> 
        if (v <= val) && (v >= 0) 
            then Just (State pkh (val-v))
            else Nothing
    _ -> Nothing

{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: Environment -> EnvironmentInput -> Maybe Environment @-}                       
withdrawFunc :: Environment -> EnvironmentInput -> Maybe Environment
withdrawFunc (Environment accts) (EnvironmentInput tth _ i) = 
    case (lookup tth accts) of
        Nothing -> Nothing
        (Just st) -> case (withdrawSM st i) of
            Nothing -> Nothing
            Just st' -> Just (Environment (insert tth st' accts))




{-@ ple withdrawPreservesOthers@-}
{-@
withdrawPreservesOthers
    ::   tth1:ThreadTokenHash
    ->   tth':ThreadTokenHash
    ->    pkh:PubKeyHash
    ->    val:Value
    -> {  env:Environment | (isJust (withdrawFunc env (EnvironmentInput tth1 tth' (Withdraw (WDArgs pkh val))))) }
    -> { tth2:ThreadTokenHash | tth2 /= tth1 }
    -> { (lookup tth2 (getAccounts env) == lookup tth2 (getAccounts (fromJust (withdrawFunc env (EnvironmentInput tth1 tth' (Withdraw (WDArgs pkh val))))))) }
@-}
withdrawPreservesOthers :: ThreadTokenHash -> ThreadTokenHash -> PubKeyHash -> Value -> Environment -> ThreadTokenHash -> Proof
withdrawPreservesOthers tth1 tth' pkh val env@(Environment accts) tth2 = 
    case lookup tth1 accts of
        Nothing -> impossible trivial
        Just s0 -> case (withdrawSM s0 (Withdraw (WDArgs pkh val))) of
            Nothing -> impossible trivial
            Just s' -> insertPreservesOthers tth1 s' accts tth2 *** QED


{-@ reflect depositSM @-}   
{-@ depositSM :: State -> AccountInput -> Maybe State @-}                
depositSM :: State -> AccountInput -> Maybe State
depositSM (State pkh val) i = case i of
    (Deposit (WDArgs pkh v)) -> 
        if v >= 0 
            then Just (State pkh (val+v)) 
            else Nothing
    _ -> Nothing 

{-@ reflect depositFunc @-}
{-@ depositFunc :: Environment -> EnvironmentInput -> Maybe Environment @-}                       
depositFunc :: Environment -> EnvironmentInput -> Maybe Environment
depositFunc (Environment accts) (EnvironmentInput tth _ i) = 
    case (lookup tth accts) of
        Nothing -> Nothing
        (Just st) -> case (depositSM st i) of
            Nothing -> Nothing
            Just st' -> Just (Environment (insert tth st' accts))


{-@ ple depositPreservesOthers@-}
{-@
depositPreservesOthers
    ::   tth1:ThreadTokenHash
    ->   tth':ThreadTokenHash
    ->    pkh:PubKeyHash
    ->    val:Value
    -> {  env:Environment | (isJust (depositFunc env (EnvironmentInput tth1 tth' (Deposit (WDArgs pkh val))))) }
    -> { tth2:ThreadTokenHash | tth2 /= tth1 }
    -> { (lookup tth2 (getAccounts env) == lookup tth2 (getAccounts (fromJust (depositFunc env (EnvironmentInput tth1 tth' (Deposit (WDArgs pkh val))))))) }
@-}
depositPreservesOthers :: ThreadTokenHash -> ThreadTokenHash -> PubKeyHash -> Value -> Environment -> ThreadTokenHash -> Proof
depositPreservesOthers tth1 tth' pkh val env@(Environment accts) tth2 =
    case lookup tth1 accts of
        Nothing -> impossible trivial
        Just s0 -> case (depositSM s0 (Deposit (WDArgs pkh val))) of
            Nothing ->  impossible trivial
            Just s' ->  insertPreservesOthers tth1 s' accts tth2 *** QED

---
{-@ ple transferSM @-}
{-@ reflect transferSM @-}
{-@ transferSM :: State -> State -> AccountInput -> Maybe (State,State) @-}                     
transferSM :: State -> State -> AccountInput -> Maybe (State,State)
transferSM (State pkh1 v1) (State pkh2 v2) i = case i of
    (Transfer (WDArgs pkh1 v)) -> 
        if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) 
            then Just ((State pkh1 (v1-v)),(State pkh2 (v2+v)))
            else Nothing
    _ -> Nothing
    
---- separate into TO and FROM

--- have it actually be plutus
--- add txinfo/constraints

---some specific haskell code to plutus

---code doesn't run?  try without state machine
--- WHAT is the library doing for me?

---look at what the issue is on State Machine formalism, 
---why is the otherwise simple looking implementation making it slow and big

---ask again WHAT IF SM are unusable?




{-@ reflect transferFunc @-}
{-@ transferFunc :: Environment -> EnvironmentInput -> Maybe Environment @-}                       
transferFunc :: Environment -> EnvironmentInput -> Maybe Environment
transferFunc (Environment accts) (EnvironmentInput tth1 tth2 i) = 
    case (lookup tth1 accts) of
        Nothing -> Nothing
        (Just st1) -> case (lookup tth2 accts) of
                Nothing -> Nothing
                (Just st2) -> case (transferSM st1 st2 i) of
                    Nothing -> Nothing
                    Just (st1',st2') -> Just (Environment (insert tth1 st1' (insert tth2 st2' accts)))




{-@ ple transferPreservesOthers@-}
{-@
transferPreservesOthers
    ::   tth1:ThreadTokenHash
    ->   tth2:ThreadTokenHash
    ->    pkh:PubKeyHash
    ->    val:Value
    -> {  env:Environment | (isJust (transferFunc env (EnvironmentInput tth1 tth2 (Transfer (WDArgs pkh val))))) }
    -> { tth3:ThreadTokenHash | tth3 /= tth1 && tth3 /= tth2 }
    -> { (lookup tth3 (getAccounts env) == lookup tth3 (getAccounts (fromJust (transferFunc env (EnvironmentInput tth1 tth2 (Transfer (WDArgs pkh val))))))) }
@-}
transferPreservesOthers :: ThreadTokenHash -> ThreadTokenHash -> PubKeyHash -> Value -> Environment -> ThreadTokenHash -> Proof
transferPreservesOthers tth1 tth2 pkh val env@(Environment accts) tth3 =
    case lookup tth1 accts of
        Nothing -> impossible trivial
        Just s1@(State pkh' v1) -> case lookup tth2 accts of
            Nothing -> impossible trivial
            Just s2@(State pkh'' v2) -> case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
                Nothing -> (case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
                                Nothing -> Nothing
                                Just (st1',st2') -> Just (Environment (insert tth1 st1' (insert tth2 st2' accts))))
                        === Nothing *** QED
--SM
--    (Transfer (WDArgs pkh1 v)) -> 
--        if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) 
--            then Just ((State pkh1 (v1-v)),(State pkh2 (v2+v)))
--            else Nothing
--    _ -> Nothing
--FUNC
--    case (lookup tth1 accts) of
--        Nothing -> Nothing
--        (Just st1) -> case (lookup tth2 accts) of
--                Nothing -> Nothing
--                (Just st2) -> case (transferSM st1 st2 i) of
--                   Nothing -> Nothing
--                   Just (st1',st2') -> Just (Environment (insert tth1 st1' (insert tth2 st2' accts)))


                Just (s1',s2') ->   lookup tth3 (getAccounts (fromJust ( case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
                                        Nothing -> Nothing
                                        Just (st1',st2') -> Just (Environment (insert tth1 st1' (insert tth2 st2' accts))))))
                                === lookup tth3 (insert tth1 s1' (insert tth2 s2' accts)) ? insertPreservesOthers tth1 s1' (insert tth2 s2' accts) tth3
                                === lookup tth3 (insert tth2 s2' accts) ? insertPreservesOthers tth2 s2' accts tth3 
                                === lookup tth3 accts *** QED





{-@ reflect openFunc @-}
{-@ openFunc :: Environment -> EnvironmentInput -> Maybe Environment @-}                       
openFunc :: Environment -> EnvironmentInput -> Maybe Environment
openFunc (Environment accts) (EnvironmentInput tth _ i) = 
    case (lookup tth accts) of
        (Just st) -> Nothing
        Nothing -> case i of
            (Open pkh) -> Just (Environment (insert tth (State pkh 0) accts))
            _ -> Nothing

{-@ ple openPreservesOthers@-}
{-@
openPreservesOthers
    ::   tth1:ThreadTokenHash
    ->   tth':ThreadTokenHash
    ->    pkh:PubKeyHash
    -> {  env:Environment | (isJust (openFunc env (EnvironmentInput tth1 tth' (Open pkh)))) }
    -> { tth2:ThreadTokenHash | tth2 /= tth1 }
    -> { (lookup tth2 (getAccounts env) == lookup tth2 (getAccounts (fromJust (openFunc env (EnvironmentInput tth1 tth' (Open pkh)))))) }
@-}
openPreservesOthers :: ThreadTokenHash -> ThreadTokenHash -> PubKeyHash -> Environment -> ThreadTokenHash -> Proof
openPreservesOthers tth1 tth' pkh env@(Environment accts) tth2 =
    case lookup tth1 accts of
        Nothing -> insertPreservesOthers tth1 (State pkh 0) accts tth2 *** QED
        _ -> () *** QED

{-@ reflect closeFunc @-}
{-@ closeFunc :: Environment -> EnvironmentInput -> Maybe Environment @-}                       
closeFunc :: Environment -> EnvironmentInput -> Maybe Environment
closeFunc (Environment accts) (EnvironmentInput tth _ i) = 
    case (lookup tth accts) of
        (Just st@(State pkh 0)) -> case i of
            (Close pkh) -> Just (Environment (delete tth accts))
            _ -> Nothing
        _ -> Nothing

{-@ ple closePreservesOthers@-}
{-@
closePreservesOthers
    ::   tth1:ThreadTokenHash
    ->   tth':ThreadTokenHash
    ->    pkh:PubKeyHash
    -> {  env:Environment | (isJust (closeFunc env (EnvironmentInput tth1 tth' (Close pkh)))) }
    -> { tth2:ThreadTokenHash | tth2 /= tth1 }
    -> { (lookup tth2 (getAccounts env) == lookup tth2 (getAccounts (fromJust (closeFunc env (EnvironmentInput tth1 tth' (Close pkh)))))) }
@-}
closePreservesOthers :: ThreadTokenHash -> ThreadTokenHash -> PubKeyHash -> Environment -> ThreadTokenHash -> Proof
closePreservesOthers tth1 tth' pkh env@(Environment accts) tth2 =
    case lookup tth1 accts of
        (Just st@(State pkh 0)) ->  lookup tth2 (getAccounts (fromJust (closeFunc env (EnvironmentInput tth1 tth' (Close pkh)))))
                                === lookup tth2 (getAccounts (fromJust (case (Close pkh) of
                                        (Close pkh) -> Just (Environment (delete tth1 accts))
                                        _ -> Nothing)))
                                === lookup tth2 (delete tth1 accts) ? deletePreservesOthers tth1 accts tth2 
                                === lookup tth2 accts*** QED
        _ -> isJust (closeFunc env (EnvironmentInput tth1 tth' (Close pkh)))
         === isJust (case (lookup tth1 accts) of
                (Just st@(State pkh 0)) -> case (Close pkh) of
                    (Close pkh) -> Just (Environment (delete tth1 accts))
                    _ -> Nothing
                _ -> Nothing)
         === isJust Nothing *** QED


--CRUX?

{-




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

{-@
xxxxx
    ::    pkh:PubKeyHash
    -> {   s0:State | isJust (transition s0 (Open pkh)) }
    -> { isJust (openFunc s0 (Open pkh)) }
@-}
xxxxx :: PubKeyHash -> State -> Proof
xxxxx pkh s0 =  transition s0 (Open pkh) *** QED
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
deletePreservesOthers pkh1 Nil pkh2 = ()
deletePreservesOthers pkh1 (Cons pkh v m) pkh2 = deletePreservesOthers pkh1 m pkh2 

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
-}

{-

{-@ ple deleteRemovesVal@-}
{-@
deleteRemovesVal
    ::   pkh:PubKeyHash
    ->   bal:AccMap PubKeyHash Value
    -> { sumVal bal - (getValue pkh bal) == sumVal (delete pkh bal)}
@-}
deleteRemovesVal :: PubKeyHash -> AccMap PubKeyHash Value -> Proof
deleteRemovesVal pkh Nil = ()
deleteRemovesVal pkh (Cons k v m) = deleteRemovesVal pkh m 

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
-}

{-

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
-}

{-

{-@ measure getBalances @-}
getBalances :: State -> AccMap PubKeyHash Value
getBalances (State bal val) = bal

{-@ reflect getValue @-}
getValue :: PubKeyHash -> AccMap PubKeyHash Value -> Value
getValue pkh bal = case lookup pkh bal of
  Just v  -> v
  Nothing -> 0

-}

{-
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
        Just v ->  () *** Admit
-- ????????????????????????
--- minimal example



    case lookup pkh1 accts of
        Nothing -> insertPreservesOthers pkh1 0 accts pkh2
        Just v -> ()

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
-}

{-

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
        _ -> () *** Admit
   

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
 
 -- lookup returns part of the sum
{-@ ple totalsLemma @-}
totalsLemma :: PubKeyHash -> Value -> AccMap PubKeyHash Value -> Value -> Proof
{-@
totalsLemma
    ::   pkh:PubKeyHash 
    ->   val:Value
    -> { bal:AccMap PubKeyHash Value | lookup pkh bal == Just val}
    -> {  tv:Value | tv == sumVal bal }
    -> { val <= tv } 
@-}
totalsLemma pkh val bal tv = () *** Admit
 
  case bal of
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
-}


{-

{-@
insertMinusVal
    ::   pkh:PubKeyHash
    ->    v0:Value
    -> { val:Value | v0 >= val }
    -> { bal:AccMap PubKeyHash Value | lookup pkh bal == Just v0 }
    -> { sumVal bal - val == sumVal (insert pkh (v0 - val) bal)}
@-}
insertMinusVal :: PubKeyHash -> Value -> Value -> AccMap PubKeyHash Value -> Proof
insertMinusVal pkh v0 val bal = () *** Admit {- sumVal (insert pkh (v0 - val) bal) ? insertModifiesByVal pkh (v0 - val) bal
                            === sumVal bal + (v0 - val) - (getValue pkh bal)
                            === sumVal bal + v0 - val - v0 
                            === sumVal bal - val *** QED -}

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
withdrawPreservesOthers pkh1 val s0@(State accts currV) pkh2 = () *** Admit


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

{-@
insertPlusVal
    ::   pkh:PubKeyHash
    ->    v0:Value
    ->   val:Value  
    -> { bal:AccMap PubKeyHash Value | lookup pkh bal == Just v0 }
    -> { sumVal bal + val == sumVal (insert pkh (v0 + val) bal)}
@-}
insertPlusVal :: PubKeyHash -> Value -> Value -> AccMap PubKeyHash Value -> Proof
insertPlusVal pkh v0 val bal  = () *** Admit {-sumVal (insert pkh (v0 + val) bal) ? insertModifiesByVal pkh (v0 + val) bal
                            === sumVal bal + (v0 + val) - (getValue pkh bal)
                            === sumVal bal + v0 + val - v0 
                            === sumVal bal + val *** QED-}

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
depositPreservesOthers pkh1 val s0@(State accts currV) pkh2 = () *** Admit

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

-- actually just InsertPresOther
{-
{-@ ple doubleInsert@-}
doubleInsert :: PubKeyHash -> Value -> PubKeyHash -> Value -> AccMap PubKeyHash Value -> Proof
{-@
doubleInsert
    ::  pkh1:PubKeyHash
    ->    v1:Value
    -> {pkh2:PubKeyHash | pkh1 /= pkh2 }
    ->    v2:Value  
    -> { bal:AccMap PubKeyHash Value | lookup pkh1 bal == Just v1 }
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
-}


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
transferPreservesOthers pkh1 pkh2 v s0@(State accts currV) pkh3 = () *** Admit


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

{-@ reflect sumVal @-}
{-@ sumVal :: AccMap PubKeyHash Value -> Value @-}
sumVal :: AccMap PubKeyHash Value -> Value
sumVal Nil = 0
sumVal (Cons k v bs) = v + sumVal bs


--lookup k2 map == lookup k2 (insert k1 val map) 

{-   

{-@ ple withdrawPreservesOthers2@-}
{-@
withdrawPreservesOthers2
    ::   tth1:ThreadTokenHash
    ->    val:Value
    -> {  env:Environment | (isJust (withdrawFunc env (EnvironmentInput tth1 (Withdraw val)))) }
    -> { tth2:ThreadTokenHash | tth2 /= tth1 }
    -> { (lookup tth2 (getAccounts env) == lookup tth2 (getAccounts (fromJust (withdrawFunc env (EnvironmentInput tth1 (Withdraw val)))))) }
@-}
withdrawPreservesOthers2 :: ThreadTokenHash -> Value -> Environment -> ThreadTokenHash -> Proof
withdrawPreservesOthers2 tth1 val env@(Environment accts) tth2 =
    case lookup tth1 accts of
        Nothing -> () *** QED
        Just s0@(State pkh v0) -> case (withdrawSM s0 (Withdraw val)) of
            Nothing ->  True
                    === (isJust (withdrawFunc env (EnvironmentInput tth1 (Withdraw val))))
                    === (isJust ( case (withdrawSM s0 (Withdraw val)) of
                                        Nothing -> Nothing
                                        Just st' -> Just (Environment (insert tth1 st' accts)))) 
                    === (isJust Nothing) *** QED
            Just s' ->  lookup tth2 (getAccounts (fromJust (withdrawFunc env (EnvironmentInput tth1 (Withdraw val))))) 
                    === lookup tth2 (getAccounts (fromJust ( case (withdrawSM s0 (Withdraw val)) of
                                        Nothing -> Nothing
                                        Just s' -> Just (Environment (insert tth1 s' accts)))))
                    === lookup tth2 (insert tth1 s' accts) ? insertPreservesOthers tth1 s' accts tth2
                    === lookup tth2 accts *** QED

            | val <= v0 && val >= 0 -> () *** Admit --PreservesOthers tth1 (fromJust (withdrawSM s0 (Withdraw val))) accts tth2 
            | otherwise -> case (withdrawSM s0 (Withdraw val)) of
                    Nothing -> () *** QED
                    Just s' -> True
                            === (isJust (withdrawFunc env (EnvironmentInput tth1 (Withdraw val))))
                            === (isJust (Just (Environment (insert tth1 s' accts)))) *** Admit


--withdrawPreservesOthers tth1 val env tth2 = () *** QED
-}


{-

{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: State -> AccountInput -> Maybe (State, Maybe Message) @-}
openFunc :: State -> AccountInput -> Maybe (State, Maybe Message)
openFunc (State accts currV) i = case i of
    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing -> 
            Just (State (insert pkh 0 accts) (currV `withProof` insertModifiesByVal pkh 0 accts)) 
    _ -> Nothing

{-@ ple closeFunc @-}
{-@ reflect closeFunc @-}  
{-@ closeFunc :: State -> AccountInput -> Maybe (State, Maybe Message) @-}                   
closeFunc :: State -> AccountInput -> Maybe (State, Maybe Message)
closeFunc (State accts currV) i = case i of
    (Close pkh) -> case lookup pkh accts `withProof` (getValue pkh accts) of
        Just 0 -> Just (State (delete pkh accts) (currV `withProof` deleteRemovesVal pkh accts))
        _ -> Nothing
    _ -> Nothing

--step in CBCAST
{-@ reflect transition @-}
{-@ transition :: Environment -> AccountInput -> Maybe Environment @-}
transition :: Environment -> AccountInput -> Maybe Environment
transition st i = case i of
--    (Open _) -> openFunc st i
--    (Close _) -> closeFunc st i               
    (Deposit _) -> depositFunc st i
    (Withdraw _) -> withdrawFunc st i
    (Transfer _) -> transferFunc st i


-}



{-

--maybe turn on ple here and test
{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: Environment -> AccountInput -> Maybe Environment @-}                       
withdrawFunc :: Environment -> AccountInput -> Maybe Environment
withdrawFunc (Environment accts) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) && (v >= 0) then
            Just (State (insert pkh (v0 - v) accts) ((currV - v) 
                `withProof` insertMinusVal pkh v0 v accts `withProof` totalsLemma pkh v0 accts currV))
                    else Nothing
    _ -> Nothing





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


-}



-}