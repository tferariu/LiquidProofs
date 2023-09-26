{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Demo.Client where

import           Prelude                                    hiding (tail, lookup, elem)
import           Data.Maybe                                 hiding (isNothing)
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

{-@ ple delete @-}
{-@ reflect delete @-}
{-@ delete :: k:key -> AccMap key val -> {accts:AccMap key val | lookup k accts = Nothing} @-}
delete :: Eq key => key -> AccMap key val -> AccMap key val
delete k1 Nil = Nil
delete k1 (Cons k0 v0 m)
    | k1 == k0 = (m `withProof` deleteDeletes k1 m)-- delete the current item
    | otherwise = Cons k0 v0 (delete k1 m) -- search to see if k1 is present

{-@ ple deleteDeletes @-}
{-@
deleteDeletes
    ::   pkh:k
    -> accts:AccMap {key:k | pkh /= key} v
    -> {lookup pkh accts == Nothing}
@-}
deleteDeletes :: Eq k => k -> AccMap k v -> Proof
deleteDeletes pkh Nil = ()
deleteDeletes pkh (Cons k v m) = deleteDeletes pkh m

{-@ ple insert @-}
{-@ reflect insert @-}
{-@ insert :: k:key -> v:val -> AccMap key val -> {accts:AccMap key val | lookup k accts = Just v} @-}
insert :: Eq key => key -> val -> AccMap key val -> AccMap key val
insert k1 v1 Nil = Cons k1 v1 Nil
insert k1 v1 (Cons k0 v0 m)
    | k1 == k0 = Cons k1 v1 m -- replace the current item
    | otherwise = Cons k0 v0 (insert k1 v1 m) -- search to see if k1 is present


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

{-@ measure getBalances @-}
getBalances :: State -> AccMap PubKeyHash Value
getBalances (State bal val) = bal

{-@ reflect getValue @-}
getValue :: PubKeyHash -> AccMap PubKeyHash Value -> Value
getValue pkh bal = case lookup pkh bal of
  Just v  -> v
  Nothing -> 0

{-

{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: State -> AccountInput -> Maybe State @-}

-}

{-@ predicate OpenPre I S = ((isOpen I) && (lookup (getPkh I) (accounts S) == Nothing)) @-}
{-@ predicate OpenPost I S1 S2 = ((isJust S2) && (lookup (getPkh I) (accounts (fromJust S2)) == Just 0)) @-}

{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (OpenPre i st1 => 
        OpenPost i st1 st2) && ((not OpenPre i st1) => (isNothing st2))}@-}
openFunc (State accts currV) i = case i of
    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing -> 
            Just (State (insert pkh 0 accts) (currV `withProof` insertModifiesByVal pkh 0 accts)) 
    _ -> Nothing

{-
{-@ predicate ClosePre I S = ((isClose I) && (isIn (getPkh I) (accounts S)) && 
            getValue (getPkh I) (accounts S) == 0 ) @-}
{-@ predicate ClosePost I S1 S2 = ((isJust S2) && not (isIn (getPkh I) (accounts (fromJust S2)))) @-}

{-@ reflect closeFunc @-}
{-@ closeFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (ClosePre i st1 => (ClosePost i st1 st2 &&
            True)) && ((not ClosePre i st1) => (isNothing st2))}@-}   
-}           
{-@ ple closeFunc @-}
{-@ reflect closeFunc @-}  
{-@ closeFunc :: State -> AccountInput -> Maybe State @-}                   
closeFunc :: State -> AccountInput -> Maybe State
closeFunc (State accts currV) i = case i of
    (Close pkh) -> case lookup pkh accts of
        Just 0 -> Just (State (delete pkh accts) (currV `withProof` deleteRemovesVal pkh accts))
        _ -> Nothing
    _ -> Nothing

--(Close pkh) -> case lookup pkh accts `withProof` (getValue pkh accts) of

{-
{-@ ple withdrawFunc @-}
{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: State -> AccountInput -> Maybe State @-}  
-}
{-@ predicate WithdrawPre I S = ((isWithdraw I) && (isIn (getPkh I) (accounts S)) && 
            getValue (getPkh I) (accounts S) >= getVal I && getVal I >= 0) @-}
{-@ predicate WithdrawPost I S1 S2 = ((isJust S2) && (isIn (getPkh I) (accounts (fromJust S2))) && 
            (getValue (getPkh I) (accounts S1)) - getVal I == (getValue (getPkh I) (accounts (fromJust S2)))) @-}

{-@ ple withdrawFunc @-}
{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | 
        (WithdrawPre i st1 => (WithdrawPost i st1 st2)) && ((not WithdrawPre i st1) => (isNothing st2))}@-}                         


                     
withdrawFunc :: State -> AccountInput -> Maybe State
withdrawFunc (State accts currV) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) && (v >= 0) then
            Just (State (insert pkh (v0 - v) accts) ((currV - v) 
                `withProof` insertModifiesByVal pkh (v0-v) accts `withProof` totalsLemma pkh v0 accts currV))
                    else Nothing
    _ -> Nothing


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
totalsLemma pkh val Nil tv = ()
totalsLemma pkh val (Cons k v m) tv 
    | pkh == k =  val + sumVal m =>= val *** QED
    | otherwise = totalsLemma pkh val m (sumVal m)
    
    

{-@ ple depositFunc@-}
{-@ reflect depositFunc @-}   
{-@ depositFunc :: State -> AccountInput -> Maybe State @-}                
depositFunc :: State -> AccountInput -> Maybe State
depositFunc (State accts currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if v >= 0 then
            Just (State (insert pkh (v0 + v) accts) (currV + v `withProof` insertModifiesByVal pkh (v0+v) accts)) 
                    else Nothing
    _ -> Nothing 


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
                    (currV `withProof` insertModifiesByVal pkh1 (v1-v) (insert pkh2 (v2 + v) accts
                    `withProof` insertPreservesOthers pkh2 (v2 + v) accts pkh1) 
                    `withProof` insertModifiesByVal pkh2 (v2+v) accts))
                else Nothing
    _ -> Nothing


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





{-@ measure isOpen @-}
isOpen :: AccountInput -> Bool
isOpen i = case i of
    (Open pkh) -> True
    _ -> False

{-@ measure isClose @-}
isClose :: AccountInput -> Bool
isClose i = case i of
    (Close pkh) -> True
    _ -> False

{-@ measure isDeposit @-}
isDeposit :: AccountInput -> Bool
isDeposit i = case i of
    (Deposit (WDArgs pkh v)) -> True
    _ -> False

{-@ measure isWithdraw @-}
isWithdraw :: AccountInput -> Bool
isWithdraw i = case i of
    (Withdraw (WDArgs pkh v)) -> True
    _ -> False

{-@ measure isTransfer @-}
isTransfer :: AccountInput -> Bool
isTransfer i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) -> True
    _ -> False

{-@ reflect isIn @-}
isIn :: PubKeyHash -> AccMap PubKeyHash Value -> Bool
isIn pkh accts = case lookup pkh accts of
  Just _  -> True
  Nothing -> False

{-@ measure getPkh @-}
getPkh :: AccountInput -> PubKeyHash
getPkh i = case i of
    (Open pkh) -> pkh
    (Close pkh) -> pkh
    (Deposit (WDArgs pkh v)) -> pkh
    (Withdraw (WDArgs pkh v)) -> pkh
    (Transfer (TransferArgs pkh1 pkh2 v)) -> pkh1

{-@ measure getPkh2 @-}
getPkh2 :: AccountInput -> PubKeyHash
getPkh2 i = case i of
    (Open pkh) -> pkh
    (Close pkh) -> pkh
    (Deposit (WDArgs pkh v)) -> pkh
    (Withdraw (WDArgs pkh v)) -> pkh
    (Transfer (TransferArgs pkh1 pkh2 v)) -> pkh2

{-@ measure getVal @-}
getVal :: AccountInput -> Value
getVal i = case i of
    (Open pkh) -> 0
    (Close pkh) -> 0
    (Deposit (WDArgs pkh v)) -> v
    (Withdraw (WDArgs pkh v)) -> v
    (Transfer (TransferArgs pkh1 pkh2 v)) -> v

{-@ measure accounts @-}
{-@ accounts:: State -> AccMap PubKeyHash Value @-}
accounts :: State -> AccMap PubKeyHash Value
accounts (State accts tv) = accts

{-@ measure totalVal @-}
{-@ totalVal:: State -> Value @-}
totalVal :: State -> Value
totalVal (State accts tv) = tv

{-@ reflect isNothing @-}
isNothing         :: Maybe a -> Bool
isNothing Nothing = True
isNothing _       = False

{-


{-
{-@ measure isOpen @-}
isOpen :: AccountInput -> Bool
isOpen i = case i of
    (Open pkh) -> True
    _ -> False

{-@ measure isClose @-}
isClose :: AccountInput -> Bool
isClose i = case i of
    (Close pkh) -> True
    _ -> False

{-@ measure isDeposit @-}
isDeposit :: AccountInput -> Bool
isDeposit i = case i of
    (Deposit (WDArgs pkh v)) -> True
    _ -> False

{-@ measure isWithdraw @-}
isWithdraw :: AccountInput -> Bool
isWithdraw i = case i of
    (Withdraw (WDArgs pkh v)) -> True
    _ -> False

{-@ measure isTransfer @-}
isTransfer :: AccountInput -> Bool
isTransfer i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) -> True
    _ -> False

{-@ reflect isIn @-}
isIn :: PubKeyHash -> AccMap PubKeyHash Value -> Bool
isIn pkh accts = case lookup pkh accts of
  Just _  -> True
  Nothing -> False

{-@ measure getPkh @-}
getPkh :: AccountInput -> PubKeyHash
getPkh i = case i of
    (Open pkh) -> pkh
    (Close pkh) -> pkh
    (Deposit (WDArgs pkh v)) -> pkh
    (Withdraw (WDArgs pkh v)) -> pkh
    (Transfer (TransferArgs pkh1 pkh2 v)) -> pkh1

{-@ measure getPkh2 @-}
getPkh2 :: AccountInput -> PubKeyHash
getPkh2 i = case i of
    (Open pkh) -> pkh
    (Close pkh) -> pkh
    (Deposit (WDArgs pkh v)) -> pkh
    (Withdraw (WDArgs pkh v)) -> pkh
    (Transfer (TransferArgs pkh1 pkh2 v)) -> pkh2

{-@ measure getVal @-}
getVal :: AccountInput -> Value
getVal i = case i of
    (Open pkh) -> 0
    (Close pkh) -> 0
    (Deposit (WDArgs pkh v)) -> v
    (Withdraw (WDArgs pkh v)) -> v
    (Transfer (TransferArgs pkh1 pkh2 v)) -> v

{-@ measure accounts @-}
{-@ accounts:: State -> AccMap PubKeyHash Value @-}
accounts :: State -> AccMap PubKeyHash Value
accounts (State accts tv) = accts

{-@ measure totalVal @-}
{-@ totalVal:: State -> Value @-}
totalVal :: State -> Value
totalVal (State accts tv) = tv

{-@ reflect isNothing @-}
isNothing         :: Maybe a -> Bool
isNothing Nothing = True
isNothing _       = False

{-
{-@ ple openFunc @-}
{-@ reflect openFunc @-}
{-@ openFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (OpenPre i st1 => 
        OpenPost i st1 st2) && ((not OpenPre i st1) => (isNothing st2))}@-}
-}

{-@ predicate OpenPre I S = ((isOpen I) && (lookup (getPkh I) (accounts S) == Nothing)) @-}
{-@ predicate OpenPost I S1 S2 = ((isJust S2) && (lookup (getPkh I) (accounts (fromJust S2)) == Just 0)) @-}

{-@ ple openCorrectness @-}
openCorrectness :: AccMap PubKeyHash Value -> Value -> PubKeyHash -> Maybe State -> Proof
{-@
openCorrectness
    ::accts:AccMap PubKeyHash Value
    ->  {tv:Value | sumVal accts == tv}
    ->  pkh:PubKeyHash
    ->  {st:Maybe State | st == openFunc (State accts tv) (Open pkh)}
    -> { ((lookup pkh accts == Nothing) => (isJust st && lookup pkh (accounts (fromJust st)) == Just 0)) &&
         (not (lookup pkh accts == Nothing) => isNothing st)  }
@-}
openCorrectness accts tv pkh st = case lookup pkh accts of
    Nothing ->  (isJust st && lookup pkh (accounts (fromJust st)) == Just 0)
            === (isJust (openFunc (State accts tv) (Open pkh)) && lookup pkh (accounts (fromJust (openFunc (State accts tv) (Open pkh)))) == Just 0) 
            === (isJust (Just (State (insert pkh 0 accts) (tv `withProof` insertModifiesByVal pkh 0 accts))) 
                && lookup pkh (accounts (fromJust (Just (State (insert pkh 0 accts) (tv `withProof` insertModifiesByVal pkh 0 accts))))) == Just 0)
            === lookup pkh (insert pkh 0 accts) == Just 0 *** Admit
    Just _ -> ()
-}

{-@ ple insertAddsAccounts @-}
{-@
insertAddsAccounts
    ::  pkh:k
    ->  val:v
    ->accts:AccMap k v
    -> {lookup pkh (insert pkh val accts) == Just val}
@-}
insertAddsAccounts :: Eq k => k -> v -> AccMap k v -> Proof
insertAddsAccounts pkh val Nil = ()
insertAddsAccounts pkh val (Cons k v m) = insertAddsAccounts pkh val m

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