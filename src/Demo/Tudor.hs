{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Demo.Tudor where

import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators

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

{-
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
