module Demo.Lib where

import Data.Ratio
import Language.Haskell.Liquid.Prelude
import GHC.Tuple
import GHC.Arr
import Data.List


{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

{-@ ex0 :: TRUE @-}
ex0 = True

{-@ ex0' :: FALSE @-}
ex0' = False

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 a b = (a && b) ==> a

{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 a b = (a && b) ==> b

{-@ ex3' :: Bool -> Bool -> TRUE @-}
ex3' a b = a  ==> (a || b)

{-@ ex4' :: Bool -> Bool -> TRUE @-}
ex4' a b = b ==> (a || b)

{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = (a && (a ==> b)) ==> b

{-@ ex7 :: Bool -> Bool -> TRUE @-}
ex7 a b = a ==> (a ==> b) ==> b

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False
-- !!
{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 a b = not (a || b) <=> (not a && not b)

{-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
exDeMorgan2 a b = not (a && b) <=> (not a || not b)

{-@ ax0 :: TRUE @-}
ax0 = 1 + 1 == 2

{-@ ax0' :: FALSE @-}
ax0' = 1 + 1 == 3

{-
{-@ ax1 :: Int -> TRUE @-}
ax1 x = (x < (x + 1))
-}
{-@ ax1' :: _ -> TRUE @-}
ax1' x = (x < (x + 1))

{-@ ax1'' :: Int -> TRUE @-}
ax1'' :: Int -> Bool
ax1'' x = (x < (x + 1))

{-@ ax2 :: Int -> TRUE @-}
ax2 :: Int -> Bool
ax2 x = (x < 0) ==> (0 <= 0 - x)

{-@ ax3 :: Int -> Int -> TRUE @-}
ax3 :: Int -> Int -> Bool
ax3 x y = (0 <= x) ==> (0 <= y) ==> (0 <= x + y)

{-@ ax4 :: Int -> Int -> TRUE @-}
ax4 :: Int -> Int -> Bool
ax4 x y = (x == y - 1) ==> (x + 2 == y + 1)


{-@ ax5 :: Int -> Int -> Int -> TRUE @-}
ax5 :: Int -> Int -> Int -> Bool
ax5 x y z =   (x <= 0 && x >= 0)
          ==> (y == x + z)
          ==> (y == z)

{-@ ax6 :: Int -> Int -> TRUE @-}
ax6 :: Int -> Int -> Bool
ax6 x y = (y >= 0) ==> (x <= x + y)

{-

{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)

{-@ congruence :: (_ -> _) -> _ -> _ -> TRUE @-}
congruence f x y = (x == y) ==> (f x == f y)

{-@ fx1 :: (Int -> Int) -> Int -> TRUE @-}
fx1 :: (Int -> Int) -> Int -> Bool
fx1 f x =   (x == f (f (f x)))
        ==> (x == f (f (f (f (f x)))))
        ==> (x == f x)

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size        :: [a] -> Int
size []     = 0
size (x:xs) = 1 + size xs        

{-@ fx0 :: [a] -> [a] -> TRUE @-}
fx0 xs ys = (xs == ys) ==> (size xs == size ys)

{-@ fx2 :: a -> [a] -> TRUE @-}
fx2 x xs = 0 < size ys
  where
    ys   = x : xs

{-@ fx2VC :: _ -> _ -> _ -> TRUE @-}
fx2VC x xs ys =   (0 <= size xs)
              ==> (size ys == 1 + size xs)
              ==> (0 < size ys)
-}

{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ one, two, three :: NonZero @-}
one   = 1 :: Int
two   = 2 :: Int
three = 3 :: Int

{-@ type Nat   = {v:Int | 0 <= v}        @-}
{-@ type Even  = {v:Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v:Int | v < 100}       @-}

{-@ zero' :: Nat @-}
zero'     = zero

{-@ zero'' :: Even @-}
zero''     = zero

{-@ zero''' :: Lt100  @-}
zero'''     = zero

{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

cannotDie = if 1 + 1 == 3
              then die "horrible death"
              else ()

{-@ divide :: Int -> NonZero -> Int @-}
divide     :: Int -> Int -> Int
divide _ 0 = die "divide by zero"
divide n d = n `div` d

avg       :: [Int] -> Int
avg []    = 0
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs

{-@ abss :: Int -> Nat @-}
abss           :: Int -> Int
abss n
  | 0 < n     = n
  | otherwise = 0 - n

result n d
  | isPositive d = "Result = " ++ show (n `divide` d)
  | otherwise    = "Humph, please enter positive denominator!"

{-@ isPositive :: x:Int -> {v:Bool | v <=> x > 0} @-}
isPositive :: Int -> Bool
isPositive x = x > 0

{-@ lAssert  :: {b:Bool| b <=> True } -> a -> a @-}
lAssert True  x = x
lAssert False _ = die "yikes, assertion fails!"

yes = lAssert (1 + 1 == 2) ()
--no  = lAssert (1 + 1 == 3) ()

truncate :: Int -> Int -> Int
truncate i max
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where
      i'       = abss i
      max'     = abss max


data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }

{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]

--badSP :: Sparse String
--badSP = SP 5 [ (0, "cat")
--             , (6, "dog") ]

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

avg2 x y   = divide (x + y)     2

avg3 x y z = divide (x + y + z) 3

size        :: [a] -> Int
size []     =  0
size (_:xs) =  1 + size xs

notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

{-@ measure notEmpty @-}

{-@ type NEList a = {v:[a] | notEmpty v} @-}

{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}

{-@ average :: NEList Int -> Int @-}
average xs = divide total elems
  where
    total  = sum xs
    elems  = size xs

average'      :: [Int] -> Maybe Int
average' xs
  | ok        = Just $ divide (sum xs) elems
  | otherwise = Nothing
  where
    elems     = size xs
    ok        = notEmpty xs


{-@ size1    :: xs:NEList a -> Pos @-}
size1        :: [a] -> Int
size1 (_:[]) =  1
size1 (_:xs) =  1 + size1 xs

{-@ size2    :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
size2        :: [a] -> Int
size2 []     =  0
size2 (_:xs) =  1 + size2 xs

{-@ headd    :: NEList a -> a @-}
headd (x:_)  = x
headd []     = die "Fear not! 'twill ne'er come to pass"

{-@ taill    :: NEList a -> [a] @-}
taill (_:xs) = xs
taill []     = die "Relaxeth! this too shall ne'er be"

safeHead      :: [a] -> Maybe a
safeHead xs
  | nulll xs   = Nothing
  | otherwise = Just $ headd xs

{-@ nulll      :: a:[a] -> {b:Bool | notEmpty a <=> (not b) } @-}
nulll []       =  True
nulll (_:_)    =  False

{-@ groupEq    :: (Eq a) => [a] -> [NEList a] @-}
groupEq :: (Eq a) => [a] -> [[a]]
groupEq []     = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys, zs)   = span (x ==) xs

-- >>> eliminateStutter "ssstringssss liiiiiike thisss"
-- "strings like this"
--{-@ eliminateStutter    :: (Eq a) => [a] -> [a] @-}
--eliminateStutter :: (Eq a) => [a] -> [a]
--eliminateStutter xs = map head $ groupEq xs

{-@ foldl11         :: (a -> a -> a) -> NEList a -> a @-}
foldl11 f (x:xs)    = foldll f x xs
foldl11 _ []        = die "foldl1"

foldll              :: (a -> b -> a) -> a -> [b] -> a
foldll _ acc []     = acc
foldll f acc (x:xs) = foldll f (f acc x) xs

{-@ sum3 :: (Num a) => NEList a -> a  @-}
sum3 []  = die "cannot add up empty list"
sum3 xs  = foldl11 (+) xs

sumOk  = sum3 [1,2,3,4,5]    -- is accepted by LH, but

--sumBad = sum3 []             -- is rejected by LH


{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage wxs = divide totElems totWeight
  where
    elems     = map (\(w, x) -> w * x) wxs
    weights   = map (\(w, _) -> w    ) wxs
    totElems  = sum elems
    totWeight = sum weights
    sum       = foldl1 (+)

{-@ mappp :: (a -> b) -> x:[a] -> {y:[b] | notEmpty x <=> notEmpty y} @-}
mappp           :: (a -> b) -> [a] -> [b]
mappp _ []      =  []
mappp f (x:xs)  =  f x : map f xs

{-@ risers       :: (Ord a) => x:[a] -> {y:[[a]] | notEmpty x <=> notEmpty y } @-}
risers           :: (Ord a) => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc)
  | x <= y       = (x:s) : ss
  | otherwise    = [x] : (s : ss)
    where
      (s, ss)    = safeSplit $ risers (y:etc)

{-@ safeSplit    :: NEList a -> (a, [a]) @-}
safeSplit (x:xs) = (x, xs)
safeSplit _      = die "don't worry, be happy"



















{-@ type Pos = {v:Int | 0 < v} @-}

{-@ incr :: Pos -> Pos @-}
incr :: Int -> Int
incr x = x + 1


{-@ type Posi = {v:Integer | 0 <= v} @-}
{-@ type Posit = {v:Integer | 0 < v} @-}
{-@ faaaa:: x:Posi -> a:Posit -> {b:Posit | b > a} -> ({y:Posi | y < x},z:Posi) @-}
faaaa :: Integer -> Integer -> Integer -> (Integer,Integer)
faaaa x a b = (((x * a) `div` b), ((x * a) `mod` b))


{-@ data Foo = Foo (x::[Integer]) {y:Integer | summ x == y} @-}
data Foo = Foo [Integer] Integer

{-@ measure summ @-}
{-@ summ :: [Integer] -> Integer @-}
summ :: [Integer] -> Integer
summ [] = 0
summ (x:xs) = x + summ xs


{-@ predicate Aux A = ((summ (fst A)) == snd A) @-}



{-@ foobar :: {a:([Integer],Integer) | Aux a} -> {b:([Integer],Integer) | Aux b} @-}
foobar :: ([Integer],Integer) -> ([Integer],Integer)
foobar ((x:xs),y) = (((x+5):xs),(y+5))
foobar dingus = dingus

{-@ barfoo :: Foo -> Foo @-}
barfoo :: Foo -> Foo
barfoo (Foo xs y) = case xs of
    x:z:xss -> (Foo (z:(x+99):xss) (y+99))
    x:xss -> (Foo ((x-6):xss) (y-6))
    [] -> Foo [7] 7



{-@ summm :: [(String, Integer)] -> Integer @-}
summm :: [(String,Integer)] -> Integer
summm [] = 0
summm ((z,x):xs) = x + summm xs


{-@ predicate Bux A B C = if (snd C == 7) then (snd B == True) else False @-}
{-@ predicate Cux A B C = (fst B == fst C) && (Bux A B C) @-}


{-}
{-@ measure summm @-}
data Assoc v = KV [(Int, v)]

{-@ data Assoc v <p :: Int -> Prop> 
    = KV (z :: [(Int<p>, v)]) @-}

    {-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}


{-@ data AccountState <p :: Int -> Prop> = AccountState (z :: [(Pkh, Value<p>)] @-}
data AccountState = AccountState [(Pkh, Value)]

--{-@ AccountStateP :: AccountState <{\x -> x >= 0}> @-}
--AccountStateP :: AccountState

{-@ type Posi = {v:Integer | 0 <= v} @-}
{-@ type Posit = {v:Integer | 0 < v} @-}
{-@ type ProperMap = [(String, Posi)] @-}
data StateP = StateP AccountStateP Value 

--{-@ data WDArgs = WDArgs String Integer<{\x -> x >= 0}>)] @-}
-}

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

{-@ impossible :: {v:_ | false} -> Int @-}
impossible :: String -> Int
impossible msg = error msg

{-@ safeDiv :: Int -> {a:Int| a /= 0} -> Int   @-}
safeDiv :: Int -> Int -> Int
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n

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