{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
--dont use ple always

{-
{-@ LIQUID "--ple-local" @-}
{-@ ple foo @-}
foo :: Int -> Int
foo _ = 5
-}

{-
inline = less constrained, but will break on recurison
         translates haskell into SMT repres verbatim, no definition, just the body
         writing so the you can reason transparently about the body
predicate deprecated?

measure = function with one argument, must pattern match on the constructor of the argument
          can be recursive (adding a refinement type to the constructor)
          becomes a constraint
^
fully understood by LH
least automated, more versatile ->
reflect = reason about the body after doing EXACTLY one expansion
-}
module Demo.PositiveValues where

import           Data.Maybe
import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators

type PubKeyHash = String
type Value = Integer

{-@ type UniqList a b = {l:[(a,b)] | noDups l} @-} --sometimes might miss that a list isn't UniqList
-- write proof that relates head and tail -> call proof when pattern matching


--{-@ type UniqList a b = [(a,b)]<{\x y -> fst x /= fst y}> @-}
-- get information on the rest of the list when pattern matching

{-@ data Balances <p :: Value -> Bool> = Balances (UniqList PubKeyHash Value<p>) @-}
data Balances = Balances [(PubKeyHash, Value)] --use data refinement instead
--maybe not use abstract refinements <>

--sumVal (Balances []) = 0
--sumVal (Balances (x:xs)) = (second x) + sumVal (Balances xs)

{-@ reflect isNothing @-}
isNothing         :: Maybe a -> Bool
isNothing Nothing = True
isNothing _       = False

{-@ measure sumVal@-}
sumVal :: Balances -> Value
sumVal (Balances xs) = sumAux xs
-- dont call a reflected function in a measure

{-@ reflect sumAux @-}
{-@ sumAux :: [(PubKeyHash, Value)] -> Value @-}
sumAux :: [(PubKeyHash, Value)] -> Value
sumAux [] = 0
sumAux (x:xs) = (second x) + sumAux xs

{-@ measure second @-}
{-@ second:: (a,b) -> b @-}
second :: (a,b) -> b
second (a,b) = b

{-@ measure first @-}
{-@ first:: (a,b) -> a @-}
first :: (a,b) -> a
first (a,b) = a

{-@ data State = State (bal:: Balances<{\x -> x >= 0}>) {v:Value | sumVal bal == v} @-}
data State = State Balances Value 

{-@ reflect lookup' @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

{-@ measure keys @-}
{-@ keys:: [(a,b)] -> Set a @-}
keys :: (Ord a) => [(a,b)] -> Set a
keys [] = empty
keys ((x,y):xs) = singleton x `union` keys xs

{-@ measure elts @-}
{-@ elts:: [(a,b)] -> (Set (a,b)) @-}
elts :: (Ord a, Ord b) => [(a,b)] -> (Set (a,b))
elts [] = empty
elts ((x,y):xs) = (singleton (x,y)) `union` elts xs

{-@ measure accounts @-}
{-@ accounts:: State -> [(PubKeyHash, Value)] @-}
accounts :: State -> [(PubKeyHash, Value)]
accounts (State (Balances bal) v) = bal

{-@ reflect noDups @-}
noDups :: (Ord a) => [(a,b)] -> Bool
noDups [] = True
noDups ((x,y):xs) | x `member` keys xs = False
                  | otherwise = noDups xs

{-
--{-@ inertia :: ks:_ -> l1:[(_, _)] -> l2:[(_, _)] -> Bool @-}
{-@ reflect inertia @-}
{-@ inertia :: ks:_ -> {l1:[(_, _)] | noDups l1} -> {l2:[(_, _)] | noDups l2} -> Bool @-}
inertia :: (Ord a, Ord b) => [a] -> [(a,b)] -> [(a,b)] -> Bool
inertia [] l1 l2 = elts l1 == elts l2
inertia (k:ks) l1 l2 = inertia ks (delete' k l1) (delete' k l2)
-} 

{-@ predicate Mem E L = member E (keys L) @-}
{-@ predicate Subset S L = (isSubsetOf (keys S) (keys L)) @-}

{-@ predicate DelSubset L2 L1 K = (Mem K L1 => (keys L1) == union (keys L2) (singleton K)) && (not (Mem K L1) => listElts L1 == listElts L2)@-}
{-@ predicate DelSubset2 L2 L1 K = (Mem K L1 => (listElts L1) == union (listElts L2) (singleton (K,specialVal L1 K))) && (not (Mem K L1) => listElts L1 == listElts L2)@-}

{-@ reflect specialVal @-}
{-@ specialVal::  l:[(_, _)] -> {k:_ | Mem k l} -> {e:_ | True} @-}
specialVal :: Eq a => [(a, b)] -> a -> b
specialVal accts pkh = case (lookup' pkh accts `withProof` lem_lookMem pkh accts) of
  Just v  -> v

-- i keyIn l1 => l1 = l2 union (singleton (i,val i in l1)) && not i keyIn l1 => l2 = l1 (set equality)
{-@ reflect delete' @-}
{-@ delete' :: i:_ -> {l1:[(_, _)] | noDups l1} -> { l2:[(_, _)] | noDups l2 && DelSubset2 l2 l1 i && Subset l2 l1 && (not (Mem i l2))} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete' x xs

--{-@refinements@-}
-- deleteClose
-- <>

{-@ reflect getValue @-}
getValue :: PubKeyHash -> [(PubKeyHash, Value)] -> Value
getValue pkh accts = case lookup' pkh accts of
  Just v  -> v
  Nothing -> 0

{-@ lem_lookMem :: k:_ -> l:_ -> { ((lookup' k l) == Nothing) <=> (not (Mem k l))} @-}
--lem_lookMem :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_lookMem :: Eq a => a -> [(a, b)] -> ()
lem_lookMem x [] = ()
lem_lookMem x ((x',y):xs) | x == x' = ()
                          | otherwise = lem_lookMem x xs

{- (Mem K L1 => (listElts L1) == union (listElts L2) (singleton (K,specialVal L1 K))) && (not (Mem K L1) => listElts L1 == listElts L2)@-}

{-@ inline add_one_elem @-}
add_one_elem :: k -> v -> [(k, v)] -> [(k, v)]
add_one_elem k v l = (k, v) : l

{-@ lem_1 :: key:PubKeyHash -> vlue:Value -> {lst:[(PubKeyHash, Value)]| not (Mem key lst)} -> { elts (delete' key (add_one_elem key vlue lst)) == elts lst  } @-}
lem_1 :: PubKeyHash -> Value -> [(PubKeyHash, Value)] -> ()
lem_1 x y [] = ()
lem_1 x y ((x',y'):xs) | x == x' = ()
                       | otherwise = lem_1 x y xs


{-@ lem_delSum :: pkh:_ -> accts:_ ->  { sumAux (delete' pkh accts) + (getValue pkh accts) = sumAux accts } @-}
lem_delSum :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_delSum x [] = ()
lem_delSum x ((x', y) : xs) | x == x'   = ()
                            | otherwise = lem_delSum x xs
                    
{-@ lem_delOth :: k1:_ -> {k2:_ | k2 /= k1 } -> t:_ ->  { ((getValue k1 t) == (getValue k1 (delete' k2 t))) } @-}
lem_delOth :: PubKeyHash -> PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_delOth a b [] = ()
lem_delOth a b ((x, y) : xs) | a == x   = ()
                             | b == x = lem_delOth a b xs
                             | otherwise = lem_delOth a b xs

{-@ lem_delOth2 :: k1:_ -> {k2:_ | k2 /= k1 } -> t:_ ->  { (isIn k1 t <=> isIn k1 (delete' k2 t)) } @-}
lem_delOth2 :: PubKeyHash -> PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_delOth2 a b [] = ()
lem_delOth2 a b ((x, y) : xs) | a == x   = ()
                              | b == x = lem_delOth2 a b xs
                              | otherwise = lem_delOth2 a b xs


{-@ lem_memIsIn :: pkh:_ -> accts:_ -> { (Mem pkh accts) <=> (isIn pkh accts)} @-}
lem_memIsIn :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_memIsIn x [] = ()
lem_memIsIn x ((x', y) : xs) | x == x'   = ()
                             | otherwise = lem_memIsIn x xs

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

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
isIn :: PubKeyHash -> [(PubKeyHash, Value)] -> Bool
isIn pkh accts = case lookup' pkh accts of
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


--((isTransfer i) && (isIn (getPkh i) (accounts st1)) && (isIn (getPkh2 i) (accounts st1)) && getValue (getPkh i) (accounts st1) >= getVal i && getVal i >= 0 && ((getPkh i) /= (getPkh2 i)) => (isJust st2) && (isIn (getPkh i) (accounts (fromJust st2))) && (isIn (getPkh2 i) (accounts (fromJust st2))) && (getValue (getPkh i) (accounts st1)) - getVal i == (getValue (getPkh i) (accounts (fromJust st2))) && (getValue (getPkh2 i) (accounts st1)) + getVal i == (getValue (getPkh2 i) (accounts (fromJust st2))))

{-@ reflect transition @-}
--{-@ transition :: State -> AccountInput -> Maybe State @-}
{-@ transition :: st1:State -> i:AccountInput -> {st2:Maybe State | (((isOpen i) && not (isIn (getPkh i) (accounts st1))) => ( (isJust st2) && (isIn (getPkh i) (accounts (fromJust st2))) && (getValue (getPkh i) (accounts (fromJust st2)) == 0))) && ( (isClose i) && (isIn (getPkh i) (accounts st1)) && (getValue (getPkh i) (accounts st1) == 0) => (isJust st2) && not (isIn (getPkh i) (accounts (fromJust st2)))) && ((isDeposit i) && (isIn (getPkh i) (accounts st1)) && getVal i >= 0 => (isJust st2) && (isIn (getPkh i) (accounts (fromJust st2))) && (getValue (getPkh i) (accounts st1)) + getVal i == (getValue (getPkh i) (accounts (fromJust st2)))) && ((isWithdraw i) && (isIn (getPkh i) (accounts st1)) && getValue (getPkh i) (accounts st1) >= getVal i => (isJust st2) && (isIn (getPkh i) (accounts (fromJust st2))) && (getValue (getPkh i) (accounts st1)) - getVal i == (getValue (getPkh i) (accounts (fromJust st2)))) && (((isTransfer i) && (isIn (getPkh i) (accounts st1)) && (isIn (getPkh2 i) (accounts st1)) && getValue (getPkh i) (accounts st1) >= getVal i && getVal i >= 0 && ((getPkh i) /= (getPkh2 i))) => (isJust st2) && (isIn (getPkh i) (accounts (fromJust st2))) && (getValue (getPkh i) (accounts st1)) - getVal i == (getValue (getPkh i) (accounts (fromJust st2))) && (isIn (getPkh2 i) (accounts (fromJust st2))) && (getValue (getPkh2 i) (accounts st1)) + getVal i == (getValue (getPkh2 i) (accounts (fromJust st2))) ) }@-}
--{-@ transition :: st1:State -> i:AccountInput -> {st2:Maybe State | ( (isClose i) && (isIn (getPkh i) (accounts st1)) && (getValue (getPkh i) (accounts st1) == 0) => (isJust st2) && not (isIn (getPkh i) (accounts (fromJust st2))))  }@-}
transition :: State -> AccountInput -> Maybe State
transition st i = case i of

    (Open _) -> openFunc st i

    (Close _) -> closeFunc st i
                  
    (Deposit _) -> depositFunc st i

    (Withdraw _) -> withdrawFunc st i

    (Transfer _) -> transferFunc st i

--    _ -> Nothing -- todo





{-@ initial :: State @-}
initial :: State
initial = State (Balances []) 0

{-@ property :: State -> [AccountInput] -> State@-}
property :: State -> [AccountInput] -> State
property st [] = st
property st (x:xs) = case (transition st x) of
    Nothing  -> property st xs
    Just st' -> property st' xs

{-@ die :: {v:_ | false} -> State @-}
die :: String -> State
die msg = error msg

{-@ reflect inertia @-}
{-@ inertia :: k:_ -> {l1:[(_, _)] | noDups l1} -> {l2:[(_, _)] | noDups l2} -> Bool @-}
inertia :: (Ord a, Ord b) => a -> [(a,b)] -> [(a,b)] -> Bool
inertia k l1 l2 = elts (delete' k l1) == elts (delete' k l2)

{-@ predicate StateInertia K S1 S2 = elts (delete' K (accounts S1)) == elts (delete' K (accounts (fromJust S2))) @-}   
--inertia K (accounts S1) (accounts (fromJust S2)) 
{-@ predicate StateInertia2 K1 K2 S1 S2 = elts (delete' K1 (delete' K2 (accounts S1))) == elts (delete' K1 (delete' K2(accounts (fromJust S2))))@-}
--inertia K1 (delete' K2 (accounts S1)) (delete' K2 (accounts (fromJust S2))) 
--            StateInertia (getPkh i) st1 st2


--add that all other accounts are still there
{-@ predicate OpenPre I S = ((isOpen I) && not (isIn (getPkh I) (accounts S))) @-}
{-@ predicate OpenPost I S1 S2 = ((isJust S2) && (isIn (getPkh I) (accounts (fromJust S2))) &&
            getValue (getPkh I) (accounts (fromJust S2)) == 0) @-}

{-@ reflect openFunc @-}
{-@ openFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (OpenPre i st1 => (OpenPost i st1 st2 && 
            True)) && ((not OpenPre i st1) => (isNothing st2))}@-}
openFunc :: State -> AccountInput -> Maybe State
openFunc (State (Balances accts) currV) i = case i of
    (Open pkh) -> case lookup' pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just (State (Balances ((((pkh, 0) : accts) `withProof` (lem_lookMem pkh accts) `withProof` (lem_1 pkh 0 accts)))) currV)
    _ -> Nothing
--StateInertia (getPkh i) st1 st2
--{-@ lem_1 :: key:PubKeyHash -> vlue:Value -> {lst:[(PubKeyHash, Value)]| not (Mem key lst)} -> { elts (delete' key (add_one_elem key vlue lst)) == elts lst  } @-}


{-@ predicate ClosePre I S = ((isClose I) && (isIn (getPkh I) (accounts S)) && 
            getValue (getPkh I) (accounts S) == 0 ) @-}
{-@ predicate ClosePost I S1 S2 = ((isJust S2) && not (isIn (getPkh I) (accounts (fromJust S2)))) @-}

{-@ reflect closeFunc @-}
{-@ closeFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (ClosePre i st1 => (ClosePost i st1 st2 &&
            True)) && ((not ClosePre i st1) => (isNothing st2))}@-}                         
closeFunc :: State -> AccountInput -> Maybe State
closeFunc (State (Balances accts) currV) i = case i of
    (Close pkh) -> case lookup' pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just (State (Balances 
                ((delete' pkh accts) `withProof` (lem_delSum pkh accts)  `withProof` 
                    (lem_memIsIn pkh (delete' pkh accts)))) currV)
                        else Nothing
    _ -> Nothing


{-@ predicate WithdrawPre I S = ((isWithdraw I) && (isIn (getPkh I) (accounts S)) && 
            getValue (getPkh I) (accounts S) >= getVal I) @-}
{-@ predicate WithdrawPost I S1 S2 = ((isJust S2) && (isIn (getPkh I) (accounts (fromJust S2))) && 
            (getValue (getPkh I) (accounts S1)) - getVal i == (getValue (getPkh i) (accounts (fromJust S2)))) @-}

{-@ reflect withdrawFunc @-}
{-@ withdrawFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (WithdrawPre i st1 => (WithdrawPost i st1 st2 &&
            StateInertia (getPkh i) st1 st2)) && ((not WithdrawPre i st1) => (isNothing st2))}@-}                         
withdrawFunc :: State -> AccountInput -> Maybe State
withdrawFunc (State (Balances accts) currV) i = case i of
    (Withdraw (WDArgs pkh v)) -> case (lookup' pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if (v <= v0) then
            Just (State (Balances 
                ((pkh, v0 - v) : ((delete' pkh accts) `withProof` (lem_delSum pkh accts)))) (currV - v))
                    else Nothing
    _ -> Nothing


{-@ predicate DepositPre I S = ((isDeposit I) && (isIn (getPkh I) (accounts S)) && getVal I >= 0) @-}
{-@ predicate DepositPost I S1 S2 = ((isJust S2) && (isIn (getPkh I) (accounts (fromJust S2))) && 
            (getValue (getPkh I) (accounts S1)) + getVal i == (getValue (getPkh i) (accounts (fromJust S2)))) @-}

{-@ reflect depositFunc @-}
{-@ depositFunc :: st1:State -> i:AccountInput -> {st2:Maybe State | (DepositPre i st1 => (DepositPost i st1 st2 &&
            StateInertia (getPkh i) st1 st2)) && ((not DepositPre i st1) => (isNothing st2))}@-}                         
depositFunc :: State -> AccountInput -> Maybe State
depositFunc (State (Balances accts) currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup' pkh accts) of
        Nothing -> Nothing
        (Just v0) -> if v >= 0 then
            Just (State (Balances 
                ((pkh, v0 + v) : ((delete' pkh accts) `withProof` (lem_delSum pkh accts)))) (currV + v))
                    else Nothing
    _ -> Nothing


--also not says other things are unmodified !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
{-@ predicate TransferPre I S = ((isTransfer I) && (isIn (getPkh I) (accounts S)) && 
            (isIn (getPkh2 I) (accounts S)) && getValue (getPkh I) (accounts S) >= getVal I && getVal I >= 0 && 
                ((getPkh I) /= (getPkh2 I))) @-}
{-@ predicate TransferPost I S1 S2 = ((isJust S2) && (isIn (getPkh I) (accounts (fromJust S2))) && 
            (getValue (getPkh I) (accounts S1)) - getVal I == (getValue (getPkh I) (accounts (fromJust S2))) && 
                (isIn (getPkh2 I) (accounts (fromJust S2))) && (getValue (getPkh2 I) (accounts S1)) + getVal I == 
                    (getValue (getPkh2 I) (accounts (fromJust S2))))@-}
--StateInertia2 (getPkh i) (getPkh2 i) st1 st2
{-@ reflect transferFunc @-}
{-@ transferFunc :: 
        st1:State -> i:AccountInput -> {st2:Maybe State | (TransferPre i st1 => (TransferPost i st1 st2 &&
        True)) && ((not TransferPre i st1) => (isNothing st2))}@-}                         
transferFunc :: State -> AccountInput -> Maybe State
transferFunc (State (Balances accts) currV) i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) -> case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then -- !!
            Just (State (Balances ( d1 `withProof` lem_delOth pkh1 pkh2 accts `withProof` lem_delOth2 pkh2 pkh1 d2 )) currV)
                                else Nothing
                where
                    d1 = (pkh1,v1-v) : (delete' pkh1 d2) `withProof` (lem_delSum pkh1 d2)
                    d2 = (pkh2,v2+v) : (delete' pkh2 accts) `withProof` (lem_delSum pkh2 accts)
    _ -> Nothing


{-
{-@ p_close :: st1:State -> {i:AccountInput | (isClose i) && (isIn (getPkh i) (accounts st1)) && (getValue (getPkh i) (accounts st1) == 0)} -> {st2:State | not (isIn (getPkh i) (accounts st2)) }@-}
p_close :: State -> AccountInput -> State
p_close (State (Balances accts) currV) i = case i of
        (Close pkh) -> case lookup' pkh accts of
            Nothing -> die "not in account map"
            (Just v0) -> if (v0 == 0) then
                (State (Balances (((delete' pkh accts) `withProof` (lem_delSum pkh accts)) `withProof` (lem_memIsIn pkh (delete' pkh accts)))) currV)
                    else die "is not zero"
        _ -> die "not Close"


{-@ p_deposit :: st1:State -> {i:AccountInput | (isDeposit i) && (isIn (getPkh i) (accounts st1)) && getVal i >= 0} -> {st2:State | (isIn (getPkh i) (accounts st2)) && (getValue (getPkh i) (accounts st1)) + getVal i == (getValue (getPkh i) (accounts st2))}@-}
p_deposit :: State -> AccountInput -> State
p_deposit (State (Balances accts) currV) i = case i of
        (Deposit (WDArgs pkh v)) -> case (lookup' pkh accts) of
                   Nothing -> die "not in account map"
                   (Just v0) -> if v >= 0 then -- !!
                       (State (Balances 
                       ((pkh, v0 + v) : (((delete' pkh accts) `withProof` (lem_delSum pkh accts)) `withProof` (lem_memIsIn pkh (delete' pkh accts))))) (currV + v))
                            else die "negative value"
        _ -> die "not Deposit"



      {-          
            
                            {st2: Maybe State | (isIn pkh1 accts) && (isIn pkh2 accts) && (getValue pkh1 accts >= v) && (v >= 0) &&
                (pkh1 /= pkh2) => (isJust st) && (isIn pkh1 (accounts (fromJust st))) && (getValue pkh1 accts) - v == 
                    (getValue pkh1 (accounts (fromJust st))) && (isIn pkh2 (accounts (fromJust st))) && 
                        (getValue pkh2 accts) + v == (getValue pkh2 (accounts (fromJust st)))}@-}



{-@ p_transfer :: 
        st1:State -> {i:AccountInput | ((isTransfer i) && (isIn (getPkh i) (accounts st1)) && 
            (isIn (getPkh2 i) (accounts st1)) && getValue (getPkh i) (accounts st1) >= getVal i && getVal i >= 0 && 
                ((getPkh i) /= (getPkh2 i)))} -> {st2:State | (isIn (getPkh i) (accounts st2)) && 
                    (getValue (getPkh i) (accounts st1)) - getVal i == (getValue (getPkh i) (accounts st2)) && 
                        (isIn (getPkh2 i) (accounts st2)) && (getValue (getPkh2 i) (accounts st1)) + getVal i == 
                            (getValue (getPkh2 i) (accounts st2))}@-}
p_transfer :: State -> AccountInput -> State
p_transfer (State (Balances accts) currV) i = case i of
    (Transfer (TransferArgs pkh1 pkh2 v)) ->        
        case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> die "pkh1 not in account map"
        (_,Nothing) -> die "pkh2 not in account map" 
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then 
            case (transition (State (Balances accts) currV) i) of
                Nothing  -> die "broken"
                Just st' -> st'
                    else die "illegal value or transfer to self"
    _ -> die "not Transfer"



{-@ p_deposit :: st1:State -> {i:AccountInput | (isDeposit i) && (isIn (getPkh i) (accounts st1)) && getVal i >= 0} -> {st2:State | (isIn (getPkh i) (accounts st2)) && (getValue (getPkh i) (accounts st1)) + getVal i == (getValue (getPkh i) (accounts st2))}@-}
p_deposit :: State -> AccountInput -> State
p_deposit (State (Balances accts) currV) i = case i of
    (Deposit (WDArgs pkh v)) -> case (lookup' pkh accts) of
        Nothing -> die "not in account map"
        (Just v0) -> if v >= 0 then 
            case (transition (State (Balances accts) currV) i) of
                Nothing  -> die "broken"
                Just st' -> st'
                    else die "negative value"
    _ -> die "not Deposit"

{-@ p_close :: st1:State -> {i:AccountInput | (isClose i) && (isIn (getPkh i) (accounts st1)) && (getValue (getPkh i) (accounts st1) == 0)} -> {st2:State | not (isIn (getPkh i) (accounts st2)) }@-}
p_close :: State -> AccountInput -> State
p_close (State (Balances accts) currV) i = case i of
    (Close pkh) -> case lookup' pkh accts of
        Nothing -> die "not in account map"
        (Just v0) -> if (v0 == 0) then
            case (transition (State (Balances accts) currV) i) of
                Nothing  -> die "broken"
                Just st' -> st'
                    else die "is not zero"
    _ -> die "not Close"

{-@ p_open :: 
        st1:State -> {i:AccountInput | (isOpen i) && not (isIn (getPkh i) (accounts st1))} ->
            {st2:State | (isIn (getPkh i) (accounts st2)) && (getValue (getPkh i) (accounts st2) == 0) }@-}
p_open :: State -> AccountInput -> State
p_open (State (Balances accts) currV) i = case i of
    (Open pkh) -> case lookup' pkh accts of
        Just _ -> die "in account map"
        Nothing -> case (transition (State (Balances accts) currV) i) of
            Nothing  -> die "broken"
            Just st' -> st'
    _ -> die "not Open"

-}
