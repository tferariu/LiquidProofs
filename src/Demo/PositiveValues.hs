{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Demo.PositiveValues where

import           Demo.Lib
import           Data.Maybe
import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators

type PubKeyHash = String
type Value = Integer


--{-@ data Balances <p :: Value -> Bool> = Balances (UniqList PubKeyHash Value<p>) @-}
{-@ data Balances <p :: Value -> Bool> = Balances [(PubKeyHash, Value<p>)] @-}
data Balances = Balances [(PubKeyHash, Value)]

{-@ measure sumVal@-}
sumVal :: Balances -> Value
sumVal (Balances xs) = sumAux xs


{-@ measure sumAux @-}
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

{-@ data State <p :: Value -> Bool> = State (bal:: Balances<p>) {v:Value | sumVal bal == v} @-}
--{-@ data State <p :: Value -> Bool> = State Balances<p> Value @-}
data State = State Balances Value 

{-@ reflect lookup' @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

{-@ reflect delete' @-}
--{-@ delete' :: _ -> UniqList _ _ -> UniqList _ _ @-}
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

{-@ lem_delete :: pkh:_ -> accts:_ ->  { sumAux (delete' pkh accts) + (value pkh accts) = sumAux accts } @-}
lem_delete :: PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_delete x [] = ()
lem_delete x ((x', y) : xs) | x == x'   = ()
                            | otherwise = lem_delete x xs
                    
{-@ lem_delOth :: k1:_ -> {k2:_ | k2 /= k1 } -> t:_ ->  { (value k1 t) = (value k1 (delete' k2 t)) } @-}
lem_delOth :: PubKeyHash -> PubKeyHash -> [(PubKeyHash, Value)] -> ()
lem_delOth a b [] = ()
lem_delOth a b ((x, y) : xs) | a == x   = ()
                             | b == x = lem_delOth a b xs
                             | otherwise = lem_delOth a b xs

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

{-@ transition :: State<{\x -> x >= 0}> -> AccountInput -> Maybe (State<{\x -> x >= 0}>)@-}
transition :: State -> AccountInput -> Maybe State
transition (State (Balances accts) currV) i = case i of

    (Open pkh) -> case lookup' pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just (State (Balances ((pkh, 0) : accts)) currV)

    (Close pkh) -> case lookup' pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just (State (Balances ((delete' pkh accts) `withProof` (lem_delete pkh accts))) currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then -- !!
                       Just (State (Balances 
                       ((pkh, v0 + v) : ((delete' pkh accts) `withProof` (lem_delete pkh accts)))) (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just (State (Balances 
                       ((pkh, v0 - v) : ((delete' pkh accts) `withProof` (lem_delete pkh accts)))) (currV - v))
                                else Nothing


    (Transfer (TransferArgs pkh1 pkh2 v)) ->        
        case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) && (pkh1 /= pkh2) then -- !!
            Just (State (Balances ( d1 `withProof` lem_delOth pkh1 pkh2 accts )) currV)
                                else Nothing
                where
                    d1 = (pkh1,v1-v) : (delete' pkh1 d2) `withProof` (lem_delete pkh1 d2)
                    d2 = (pkh2,v2+v) : (delete' pkh2 accts) `withProof` (lem_delete pkh2 accts)

--    _ -> Nothing -- todo

{-@ initial :: Balances @-}
initial :: Balances
initial = Balances []