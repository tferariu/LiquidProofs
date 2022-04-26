module Demo.StateMachines where

import Demo.Lib
import Data.Maybe

type PubKeyHash = String
type Value = Integer

{-@ data Balances = Balances [(PubKeyHash, Value<{\x -> x >= 0}>)] @-}
data Balances = Balances [(PubKeyHash, Value)]

lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete' x xs

data TransferArgs = TransferArgs PubKeyHash PubKeyHash Value

data WDArgs = WDArgs PubKeyHash Value

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open PubKeyHash
    | Close PubKeyHash

{-@ transition :: (Balances, Value) -> AccountInput -> Maybe (Balances, Value)@-}
transition :: (Balances, Value) -> AccountInput -> Maybe (Balances, Value)
transition ((Balances accts), currV) i = case i of

    (Open pkh) -> case lookup' pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just ((Balances ((pkh, 0) : accts)), currV)

    (Close pkh) -> case lookup' pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just ((Balances (delete' pkh accts)), currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then -- !!
                       Just ((Balances ((pkh, v0 + v) : (delete' pkh accts))), (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just ((Balances ((pkh, v0 - v) : (delete' pkh accts))),
                             (currV - v))
                                else Nothing

    (Transfer (TransferArgs pkh1 pkh2 v)) -> case ((lookup' pkh1 accts),(lookup' pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) then -- !!
            Just ((Balances ((pkh1, v1 - v) : (delete' pkh1 ((pkh2, v2 + v) : (delete' pkh2 accts))))), currV)
                                else Nothing

--    _ -> Nothing -- todo


{-@ initial :: Balances @-}
initial :: Balances
initial = Balances []