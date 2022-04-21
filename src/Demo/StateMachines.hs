module Demo.StateMachines where

import Demo.Lib
import Data.Maybe

lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

delete :: Eq a => a -> [(a, b)] -> [(a, b)]
delete x [] = []
delete x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete x xs


type Pkh = String
type Value = Integer

{-}

data Assoc v = KV [(Int, v)]

{-@ data Assoc v <p :: Int -> Prop> 
    = KV (z :: [(Int<p>, v)]) @-}

    {-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}


{-@ data AccountState <p :: Int -> Prop> = AccountState (z :: [(Pkh, Value<p>)] @-}
data AccountState = AccountState [(Pkh, Value)]

--{-@ AccountStateP :: AccountState <{\x -> x >= 0}> @-}
--AccountStateP :: AccountState
-}

{-@ data AccountStateP = AccountStateP [(Pkh, Value<{\x -> x >= 0}>)] @-}
{-@ data AccountStateB = AccountStateB [(Pkh, Value<{\x -> x < 0}>)] @-}
data AccountStateP = AccountStateP [(Pkh, Value)]
data AccountStateB = AccountStateB [(Pkh, Value)]

data StateP = StateP AccountStateP Value 

{-@ type Posi = {v:Integer | 0 <= v} @-}
{-@ type Posit = {v:Integer | 0 < v} @-}
{-@ type ProperMap = [(String, Posi)] @-}


data TransferArgs = TransferArgs Pkh Pkh Value

--{-@ data WDArgs = WDArgs String Integer<{\x -> x >= 0}>)] @-}
data WDArgs = WDArgs Pkh Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open Pkh
    | Close Pkh

{-@ transition :: AccountStateP -> Value -> AccountInput -> t:(Maybe (AccountStateP, Value))@-}
transition :: AccountStateP -> Value -> AccountInput -> Maybe (AccountStateP, Value)
transition (AccountStateP accts) currV i = case i of

    (Open pkh) -> case lookup' pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just ((AccountStateP ((pkh, 0) : accts)), currV)

    (Close pkh) -> case lookup' pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just ((AccountStateP (delete pkh accts)), currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then
                       Just ((AccountStateP ((pkh, v0 + v) : (delete pkh accts))), (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just ((AccountStateP ((pkh, v0 - v) : (delete pkh accts))),
                             (currV - v))
                                else Nothing

    (Transfer (TransferArgs pkh1 pkh2 v)) -> case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) then
            Just ((AccountStateP ((pkh1, v1 - v) : (delete pkh1 ((pkh2, v2 + v) : (delete pkh2 accts))))), currV)
                                else Nothing

    _ -> Nothing -- todo


{-@ initial :: AccountStateP @-}
initial :: AccountStateP
initial = AccountStateP []