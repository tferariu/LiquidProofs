{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.MessagesUTxO where

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
        Nothing -> () *** QED
        Just s0 -> case (withdrawSM s0 (Withdraw (WDArgs pkh val))) of
            Nothing ->  True
                    === (isJust (withdrawFunc env (EnvironmentInput tth1 tth' (Withdraw (WDArgs pkh val)))))
                    === (isJust ( case (withdrawSM s0 (Withdraw (WDArgs pkh val))) of
                                        Nothing -> Nothing
                                        Just st' -> Just (Environment (insert tth1 st' accts)))) 
                    === (isJust Nothing) *** QED
            Just s' ->  lookup tth2 (getAccounts (fromJust (withdrawFunc env (EnvironmentInput tth1 tth' (Withdraw (WDArgs pkh val)))))) 
                    === lookup tth2 (getAccounts (fromJust ( case (withdrawSM s0 (Withdraw (WDArgs pkh val))) of
                                        Nothing -> Nothing
                                        Just s' -> Just (Environment (insert tth1 s' accts)))))
                    === lookup tth2 (insert tth1 s' accts) ? insertPreservesOthers tth1 s' accts tth2
                    === lookup tth2 accts *** QED


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
        Nothing -> () *** QED
        Just s0 -> case (depositSM s0 (Deposit (WDArgs pkh val))) of
            Nothing ->  True
                    === (isJust (depositFunc env (EnvironmentInput tth1 tth' (Deposit (WDArgs pkh val)))))
                    === (isJust ( case (depositSM s0 (Deposit (WDArgs pkh val))) of
                                        Nothing -> Nothing
                                        Just st' -> Just (Environment (insert tth1 st' accts)))) 
                    === (isJust Nothing) *** QED
            Just s' ->  lookup tth2 (getAccounts (fromJust (depositFunc env (EnvironmentInput tth1 tth' (Deposit (WDArgs pkh val)))))) 
                    === lookup tth2 (getAccounts (fromJust ( case (depositSM s0 (Deposit (WDArgs pkh val))) of
                                        Nothing -> Nothing
                                        Just st' -> Just (Environment (insert tth1 st' accts)))))
                    === lookup tth2 (insert tth1 s' accts) ? insertPreservesOthers tth1 s' accts tth2
                    === lookup tth2 accts *** QED

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
        Nothing -> () *** QED
        Just s1@(State pkh' v1) -> case lookup tth2 accts of
            Nothing -> () *** QED
            Just s2@(State pkh'' v2) -> case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
                Nothing ->  True
                        === (isJust (transferFunc env (EnvironmentInput tth1 tth2 (Transfer (WDArgs pkh val)))))
                        === (isJust ( case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
                                            Nothing -> Nothing
                                            Just (st1',st2') -> Just (Environment (insert tth1 st1' (insert tth2 st2' accts))))) 
                        === (isJust Nothing) *** QED
                Just (s1',s2') ->   lookup tth3 (getAccounts (fromJust (transferFunc env (EnvironmentInput tth1 tth2 (Transfer (WDArgs pkh val)))))) 
                                === lookup tth3 (getAccounts (fromJust ( case (transferSM s1 s2 (Transfer (WDArgs pkh val))) of
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
