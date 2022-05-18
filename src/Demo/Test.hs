module Demo.Test where

import Data.Set

{-@ measure sumAux @-}
{-@ sumAux :: [(String, Int)] -> Int @-}
sumAux :: [(String, Int)] -> Int
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

{-@ predicate Elem E L = (member E (listElts L)) @-}

--{-@ reflect lookup' @-}
{-@ lookup' :: i:_ -> l:[(_, _)] -> {v0 : Maybe _ | ( isJust v0 ==> (Elem (i,(fromJust v0)) l) )} @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

--{-@ delete' :: x:_ -> xs:[(_,_)] -> {r : [(_,_)] | Elem (x,v) xs ==> ((sumAux xs) - v == sumAux r) } @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete' x xs

{-@ type CorrectResult = {v:([(String, Int)],Int) | sumAux (first v) == second v}@-}

{-@ deposit :: Int -> String -> balances:[(String, Int)] -> {total:Int | sumAux balances == total} -> Maybe CorrectResult @-}
deposit :: Int -> String -> [(String, Int)] -> Int -> Maybe ([(String, Int)],Int)
deposit v pkh accts currV = 
    case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then 
                       Just ( ((pkh, v0 + v) : (delete' pkh accts)) , (currV + v))
                            else Nothing