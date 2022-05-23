{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Demo.Test where

import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators
import           Data.Maybe

{-}
{-@ measure sumAux @-}
{-@ sumAux :: [(String, Int)] -> Int @-}
sumAux :: [(String, Int)] -> Int
sumAux [] = 0
sumAux (x:xs) = (second x) + sumAux xs
-}

{-@ measure second @-}
{-@ second:: (a,b) -> b @-}
second :: (a,b) -> b
second (a,b) = b

{-@ measure first @-}
{-@ first:: (a,b) -> a @-}
first :: (a,b) -> a
first (a,b) = a

{-@ measure firsts @-}
{-@ firsts:: [(a,b)] -> [a] @-}
firsts :: [(a,b)] -> [a]
firsts [] = []
firsts ((a,b):xs) = a:(firsts xs)

{-@ measure keys @-}
{-@ keys:: [(a,b)] -> Set a @-}
keys :: (Ord a) => [(a,b)] -> Set a
keys [] = empty
keys ((x,y):xs) = singleton x `union` keys xs

{-@ measure noDups @-}
noDups :: (Ord a) => [(a,b)] -> Bool
noDups [] = True
noDups ((x,y):xs) | x `member` keys xs = False
                  | otherwise = noDups xs

{-@ predicate FstElem E L = (member (first E) (listElts (firsts L))) @-}
{-@ predicate FstSubset S L = (isSubsetOf (listElts (firsts S)) (listElts (firsts L))) @-}

{-@ reflect lookup' @-}
--{-@ lookup' :: i:_ -> l:[(_, _)] -> {v0 : Maybe _ | ( isJust v0 ==> (Elem (i,(fromJust v0)) l) )} @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

{-@ type UniqList a b = [(a,b)]<{\xi xj -> (first xi) /= (first xj)}> @-}

{-@ predicate Subset S L = (isSubsetOf (listElts S) (listElts L)) @-}

--{-@ delete' :: _ -> UniqList _ _ -> UniqList _ _ @-}
--{-@ delete' :: x:_ -> xs:UniqList _ _ -> {r : UniqList _ _ | FstSubset r xs } @-}
--{-@ delete' :: x:_ -> xs:UniqList _ _ -> {r : UniqList _ _ | isSubsetOf (listElts r) (listElts xs) } @-}


{-@ predicate Mem E L = member E (listElts L) @-}

{-@ reflect delete' @-}
--{-@ delete' :: i:_ -> {l1:[(_, _)] | noDups l1} -> { l2:[(_, _)] | noDups l2 && Subset l2 l1} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = ((x', y) : delete' x xs) `withProof` (lem1 x xs (x', y))


{-@ lem1 :: k:_ -> xs:_ -> {e:_ | not (Mem e xs)} -> { not (Mem e (delete' k xs)) } @-}
lem1 :: Eq a => a -> [(a, b)] -> (a, b) -> ()
lem1 k [] e = ()
lem1 k ((x, y) : xs) e | k == x = ()
                       | otherwise =  lem1 k xs e

{-}
k
((x, y) : xs) 
not Mem e (x, y) : xs
not Mem e (delete' k xs)

not Mem e (delete' k ((x, y) : xs))


k == x =>  (delete' k ((x, y) : xs)) -> xs     
! not Mem e xs
^
not Mem e (x, y) : xs


k /=x =>  (delete' k ((x, y) : xs)) -> (x,y) : delete' k xs  

! not Mem e ((x,y) : delete' k xs )

not Mem e (delete' k xs)
-}



--{-@ lem2 :: k:_ -> xs:_ -> { Subset ( (delete' k xs)) ( xs) } @-}
lem2 :: Eq a => a -> [(a, b)] -> ()
lem2 k [] = ()
lem2 k ((x, y) : xs) | x == k   = ()
                     | otherwise = lem2 k xs



{-

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





{-@ lem_Uniq :: -> t:_ ->  { sumAux (delete' k t) + (value k t) = sumAux t } @-}
lem_Uniq :: [(a, b)] -> ()
lem_Uniq x [] = ()
lem_Uniq x ((x', y) : xs) | x == x'   = ()
                            | otherwise = lem_delete x xs


{-@ type CorrectResult = {v:([(String, Int)],Int) | sumAux (first v) == second v}@-}

--{-@ deposit :: Int -> String -> balances:[(String, Int)] -> {total:Int | sumAux balances == total} -> Maybe CorrectResult @-}
deposit :: Int -> String -> [(String, Int)] -> Int -> Maybe ([(String, Int)],Int)
deposit v pkh accts currV = 
    case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then 
                       Just ( ((pkh, v0 + v) : (delete' pkh accts)) , (currV + v))
                            else Nothing

-}