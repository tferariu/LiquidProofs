module Demo.Lib where

import Data.Ratio
import Language.Haskell.Liquid.Prelude (isEven)


{-@ type Pos = {v:Int | 0 < v} @-}

{-@ incr :: Pos -> Pos @-}
incr :: Int -> Int
incr x = x + 1


{-@ type Posi = {v:Integer | 0 <= v} @-}
{-@ type Posit = {v:Integer | 0 < v} @-}
{-@ faaaa:: x:Posi -> a:Posit -> {b:Posit | b > a} -> ({y:Posi | y < x},z:Posi) @-}
faaaa :: Integer -> Integer -> Integer -> (Integer,Integer)
faaaa x a b = (((x * a) `div` b), ((x * a) `mod` b))


{-@ baaaa:: a:(Posi,Posi) -> ({y:Posi | y == (snd a)},{z:Posi | z == (fst a)}) @-}
baaaa :: (Integer,Integer) -> (Integer,Integer)
baaaa (a, b) = (b,a)

data Assoc v = KV [(Int, v)]
{-@ data Assoc v <p :: Int -> Bool> = KV (z :: [(Int<p>, v)]) @-} 

{-
{-@ data Mememe <p :: Meme -> Int -> Bool> = Scamboli (z :: Meme) x::(Int<p z>) @-}
data Mememe = Scamboli Meme Integer
data Meme = MC [(String, Integer)]



{-@ data AccountStateP = AccountStateP [(Pkh, Value<{\x -> x >= 0}>)] @-}
{-@ data AccountStateB = AccountStateB [(Pkh, Value<{\x -> x < 0}>)] @-}
data AccountStateP = AccountStateP [(Pkh, Value)]
data StateP = StateP AccountStateP Value 

data (a,b)<p :: a -> b -> Prop> = (x:a, b<p x>) 

 {-@ break :: (a -> Bool) -> x:[a] 
248:           -> ([a], [a])<{\y z -> (Break x y z)}> @-}

{-@ predicate Bux A B C = if (snd C == 7) then (snd B == True) else False @-}
{-@ predicate Aux A B C = (fst B == fst C) && (Bux A B C) @-}

{-@ caaaa:: {a:(Posi,Posi)| fst a == snd a} -> ((Posi, Bool),(Posi, Posi))<{\b c -> Aux a b c}> @-}
caaaa :: (Integer,Integer) -> ((Integer,Bool),(Integer,Integer))
caaaa (a, b) = case 7 of 
  7 -> ((b,True),(a,7))
  _ -> ((1,False),(-4,8))
-}

{-
{-@ type Posi = {v:Int | 0 <= v} @-}
{-@ bingus :: Posi -> Posi -> Posi -> Posi @-}
bingus :: Integer -> Integer -> Integer -> Integer
bingus x y z = (x * y) `div` z'
  where
    z' = if z == 0 then 1 else z

{-@ posify :: Integer -> Posi @-}
posify :: Integer -> Integer
posify x = if x >= 0 then x
                      else -x 


tst x r = bingus (posify x) (posify (numerator r)) (posify (denominator r))
-}

{-
{-@ bar :: AccountState -> Bool @-}
bar :: AccountState -> Bool
bar (AccountState (acc,_)) = all (\x -> (snd x) >= 0) acc

{-@ foo :: {a:AccountState | bar a} -> [Posi] @-}
foo :: AccountState -> [Integer]
foo (AccountState (acc,_)) = map snd acc

test2 :: [(String, Integer)] -> Bool
{-@ foo :: AS -> [Posi] @-}
foo :: AS -> [Integer]
foo (AS acc) = map snd acc


{-@mapCheck :: (ProperMap,Whatever) -> {b: Bool | b == True}@-}
mapCheck :: ([(String, Integer)],[(String, (Integer, Integer))]) -> Bool
mapCheck (acts, lb) = scrungus acts

{-@scrungus :: ProperMap -> {b: Bool | b == True}@-}
scrungus :: [(String, Integer)] -> Bool
scrungus [] = True
scrungus (x:xs) = if snd x >= 0 then scrungus xs else False

-}

{-
maximumPoly :: (Ord a) => [a] -> a
maximumPoly (x:xs) = foldr maxPoly x xs

maxPoly     :: (Ord a) => a -> a -> a 
maxPoly x y = if x <= y then y else x

--{-@ isEven :: x:Int -> {v:Bool | v == Even x} @-}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0

{-@ predicate Even X = ((X mod 2) = 0) @-}
{-@ maxEvens2 :: xs:[Int] -> {v:Int | (Even v) } @-}
maxEvens2 xs = maximumPoly xs''
  where 
    xs'     = [ x | x <- xs, isEven x]
    xs''    = 0 : xs'
-}







{-

{-@ data AccountState = AccountState ([(String, Integer)], [(String, (Integer, Integer))]) @-}

data AccountState = AccountState ([(String, Integer)], [(String, (Integer, Integer))])




{-@ abs :: Int -> {v:Int | v >= 0} @-}
abs :: Int -> Int
abs x
  | x < 0     = - x
  | otherwise = x

{-@ sub :: i:Nat -> {j:Nat | i >= j} -> {v:Nat | v >= 0} @-}
sub :: Int -> Int -> Int
sub i j = i - j

{-@ halve:: i : Int -> { t : (Int, Int) | i == (fst t + snd t) }@-}
halve :: Int -> (Int, Int)
halve i = (j, j + r)
  where
    j = i `div` 2
    r = i `mod` 2



data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`

{-@ lengt :: List a -> Nat @-}
lengt :: List a -> Int
lengt Nil           = 0
lengt (x `Cons` xs) = 1 + lengt xs

{-@ measure lengt @-}  
{-@ data List [lengt] @-}

{-@ mapp:: (a->b) -> l1: List a -> {l2: List b | lengt l1 == lengt l2}@-}
mapp :: (a -> b) -> List a -> List b
mapp _ Nil           = Nil
mapp f (x `Cons` xs) = f x `Cons` mapp f xs

{-@ interleave :: xs : List a -> ys : List a -> {zs: List a | lengt zs == lengt xs + lengt ys} / [lengt xs + lengt ys] @-}
interleave :: List a -> List a -> List a
interleave Nil           ys  = ys
interleave xs            Nil = xs
interleave (x `Cons` xs) ys  = x `Cons` interleave ys xs

{-@ hed:: {l: List a | lengt l > 0} -> a @-}
hed :: List a -> a
hed (Cons x xs) = x

{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible msg = error msg

{-@ tail:: {l: List a | lengt l > 0} -> List a @-}
tail :: List a -> List a
tail (Cons x xs) = xs

--{-@ tak :: i : Nat -> {xs : List a | lengt xs >= i} -> { ys : List a | lengt ys == i } @-}
{-@ tak :: i : Nat -> xs : List a -> { ys : List a | lengt ys == i || ( lengt xs < i && lengt ys == lengt xs) } @-}
tak :: Int -> List a -> List a
tak _ Nil         = Nil
tak 0 _           = Nil
tak i (Cons x xs) =
  x `Cons` tak (i - 1) xs

{-@ drp :: i : Nat -> xs : List a -> { ys : List a | lengt ys == lengt xs - i || (lengt xs < i && lengt ys == 0)} @-}
drp :: Int -> List a -> List a
drp _ Nil         = Nil
drp 0 xs          = xs
drp i (Cons _ xs) =
  drp (i - 1) xs

{-@ sublst :: Nat -> Nat -> List a -> List a @-}
sublst :: Int -> Int -> List a -> List a
sublst s l xs = tak l (drp s xs)

testSublist1 :: List Int
testSublist1 = sublst 1 2 (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil) -- ok

testSublist2 :: List Int
testSublist2 = sublst 2 3 (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil) -- should fail

{-@replicat :: i: Nat -> a -> {xs : List a | lengt xs == i} @-}
replicat :: Int -> a -> List a
replicat i x
  | i == 0    = Nil
  | otherwise = x `Cons` replicat (i - 1) x

test1 :: Int
test1 = hed (replicat 3 3)

test2 :: List Int
test2 = tak (hed (replicat 3 3)) (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil)

{- ????-}
{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ weAreEven :: [Even] @-}
weAreEven     = [(0-10), (0-4), 0, 2, 666]

{-@ notEven :: Even @-}
notEven = 8

{-@ isEven :: n:Nat -> {v:Bool | (v <=> (n mod 2 == 0))} @-}   
isEven   :: Int -> Bool 
isEven 0 = True
isEven 1 = False
isEven n = not (isEven (n-1))

{-@ evens :: n:Nat -> [Even] @-}
evens n = [i | i <- range 0 n, isEven i] 

{-@ range :: lo:Int -> hi:Int -> [{v:Int | (lo <= v && v < hi)}] / [hi -lo] @-}
range lo hi 
  | lo < hi   = lo : range (lo+1) hi
  | otherwise = []
  
{-@ shift :: [Even] -> Even -> [Even] @-}
shift xs k = [x + k | x <- xs]

{-@ double :: [Nat] -> [Even] @-}
double xs = [x + x | x <- xs]



---

notEven    :: Int
weAreEven  :: [Int]
shift      :: [Int] -> Int -> [Int]
double     :: [Int] -> [Int]
range      :: Int -> Int -> [Int]







-}