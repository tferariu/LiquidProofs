{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Demo.UniqList where

import           Data.Maybe
import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators

type PubKeyHash = String
type Value = Integer


{-@ type UniqList a b = {l:[(a,b)] | noDups l} @-}

{-@ data Balances = Balances (UniqList PubKeyHash Value) @-}
data Balances = Balances [(PubKeyHash, Value)]

{-@ measure second @-}
{-@ second:: (a,b) -> b @-}
second :: (a,b) -> b
second (a,b) = b

{-@ measure first @-}
{-@ first:: (a,b) -> a @-}
first :: (a,b) -> a
first (a,b) = a

{-@ data State = State Balances Value @-}
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

{-@ reflect noDups @-}
noDups :: (Ord a) => [(a,b)] -> Bool
noDups [] = True
noDups ((x,y):xs) | x `member` keys xs = False
                  | otherwise = noDups xs

{-@ predicate Mem E L = member E (keys L) @-}
{-@ predicate Subset S L = (isSubsetOf (keys S) (keys L)) @-}

{-@ reflect delete' @-}
{-@ delete' :: i:_ -> {l1:[(_, _)] | noDups l1} -> { l2:[(_, _)] | noDups l2 && Subset l2 l1 && (not (Mem i l2))} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete' x xs

{-@ reflect value @-}
value :: PubKeyHash -> [(PubKeyHash, Value)] -> Value
value pkh accts = case lookup' pkh accts of
  Just v  -> v
  Nothing -> 0

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

{-@ lem1 :: k:_ -> l:_ -> { ((lookup' k l) == Nothing) <=> (not (Mem k l))} @-}
lem1 :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem1 x [] = ()
lem1 x ((x',y):xs) | x == x' = ()
                   | otherwise = lem1 x xs

{-@ transition :: State -> AccountInput -> Maybe State@-}
transition :: State -> AccountInput -> Maybe State
transition (State (Balances accts) currV) i = case i of

    (Open pkh) -> case lookup' pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just (State (Balances (((pkh, 0) : accts) `withProof` (lem1 pkh accts))) currV)

    (Close pkh) -> case lookup' pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just (State (Balances ((delete' pkh accts))) currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then -- !!
                       Just (State (Balances 
                       ((pkh, v0 + v) : ((delete' pkh accts)))) (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just (State (Balances 
                       ((pkh, v0 - v) : ((delete' pkh accts)))) (currV - v))
                                else Nothing


    (Transfer (TransferArgs pkh1 pkh2 v)) ->        
        case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then -- !!
            Just (State (Balances ( d1 )) currV)
                                else Nothing
                where
                    d1 = (pkh1,v1-v) : (delete' pkh1 d2)
                    d2 = (pkh2,v2+v) : (delete' pkh2 accts)

--    _ -> Nothing -- todo

{-@ initial :: Balances @-}
initial :: Balances
initial = Balances []