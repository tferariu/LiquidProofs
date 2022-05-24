{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Demo.Test where

import           Data.Set
import           Language.Haskell.Liquid.ProofCombinators
import           Data.Maybe

{-@ reflect sumAux @-}
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

{-@ predicate Mem E L = member E (keys L) @-}
{-@ predicate Subset S L = (isSubsetOf (keys S) (keys L)) @-}

{-@ reflect lookup' @-}
lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup' x xs

{-@ reflect delete' @-}
{-@ delete' :: i:_ -> {l1:[(_, _)] | noDups l1} -> { l2:[(_, _)] | noDups l2 && Subset l2 l1 && (not (Mem i l2))} @-}
delete' :: Eq a => a -> [(a, b)] -> [(a, b)]
--delete' :: String -> [(String, Int)] -> [(String, Int)]
delete' x [] = []
delete' x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = ((x', y) : delete' x xs)


{-@ lem10 :: k:_ -> xs:_ -> {e:_ | not (Mem e xs)} -> { not (Mem e (delete' k xs)) } @-}
lem10 :: Eq a => a -> [(a, b)] -> a -> ()
lem10 k [] e = ()
lem10 k ((x, y) : xs) e | k == x = ()
                        | otherwise =  lem10 k xs e



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


{-@ lem3 :: k:_ -> l:_ -> { ((lookup' k l) == Nothing) <=> (not (Mem k l))} @-}
lem3 :: String -> [(String, Int)] -> ()
lem3 x [] = ()
lem3 x ((x',y):xs) | x == x' = ()
                   | otherwise = lem3 x xs



{-

{-@ lem2' :: k:_ -> l:_ -> { not (Mem k (delete' k l))} @-}
lem2' :: Eq a => a -> [(a, b)] -> ()
lem2' k [] = ()
lem2' k ((x, y) : xs) | x == k   = ()
                      | otherwise = lem2' k xs

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

-}
--{-@ data Balances <p :: Value -> Bool> = Balances (UniqList PubKeyHash Value<p>) @-}
--{-@ data Balances = Balances [(PubKeyHash, Value)]<{\x -> noDups x}> @-}
--{-@ data State = State (bal:: Balances) {v:Value | sumVal bal == v} @-}

{-@ type UniqList a b = {l:[(a,b)] | noDups l} @-}

{-@ data Balances = Balances {n::UniqList String Int} @-}
data Balances = Balances [(String, Int)]

{-@ type CorrectResult = {v:([(String, Int)],Int) | noDups (first v)}@-}

{-@ deposit :: Int -> String -> {balances:[(String, Int)] | noDups balances} -> total:Int -> Maybe CorrectResult @-}
deposit :: Int -> String -> [(String, Int)] -> Int -> Maybe ([(String, Int)],Int)
deposit v pkh accts currV = 
    case (lookup' pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then 
                       Just ( ( (delete' pkh accts)) , (currV + v))
                            else Nothing

