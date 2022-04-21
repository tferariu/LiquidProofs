module Demo.Lob where

import Demo.Lib
import Data.Ratio
import Data.Maybe

lookup' :: Eq a => a -> [(a, b)] -> Maybe b
lookup' x [] = Nothing
lookup' x ((x', y):xs)
    | x == x'   = Just y
    | otherwise = lookup x xs

delete :: Eq a => a -> [(a, b)] -> [(a, b)]
delete x [] = []
delete x ((x', y) : xs)
    | x == x'   = xs
    | otherwise = (x', y) : delete x xs

findLO :: Eq a => Eq b => Eq c => ((a,d),(b,c)) -> [(a,(b, c))] -> Bool
findLO x [] = False
findLO ((u,f),(p,s)) (y:ys)
    | (u,(p,s)) == y = True
    | otherwise = findLO ((u,f),(p,s)) ys

checkLO :: Eq a => Eq b => Eq c =>  [((a,d),(b,c))] -> [(a,(b, c))] -> Bool
checkLO xs [] = False
checkLO [] ys = True
checkLO (x:xs) ys
    | findLO x ys = checkLO xs ys
    | otherwise = False

deleteLO :: Eq a => Eq b => Eq c =>  (a,(b,c)) -> [(a,(b, c))] -> [(a,(b, c))]
deleteLO x [] = []
deleteLO x (y:ys)
    | x == y = ys
    | otherwise = y : (deleteLO x ys)

cleanLO :: Eq a => Eq b => Eq c =>  [((a,r),(b,c))] -> [(a,(b, c))] -> [(a,(b, c))]
cleanLO xs [] = []
cleanLO [] ys = ys
cleanLO (((u,f),(p,s)):xs) ys = cleanLO xs (deleteLO (u,(p,s)) ys)


--{-@ data AccountState = AccountState ([(String, Integer)], [(String, (Integer, Integer))]) @-}
--type pk = String && Value = Integer

--data AccountState = AccountState ([(PKH, Value)], [(PKH, (Value, Value))])

{-@ data AccountStateP = AccountStateP [(String, Integer<{\x -> x >= 0}>)] [(String, (Integer<{\x -> x >= 0}>, Integer<{\x -> x >= 0}>))] @-}
{-@ data AccountStateB = AccountStateB [(String, Integer<{\x -> x < 0}>)] [(String, (Integer<{\x -> x < 0}>, Integer<{\x -> x < 0}>))] @-}
data AccountStateP = AccountStateP [(String, Integer)] [(String, (Integer, Integer))]
data AccountStateB = AccountStateB [(String, Integer)] [(String, (Integer, Integer))]
data ProperState = ProperState [(String, Integer)] [(String, (Integer, Integer))]
data BadState = BadState [(String, Integer)] [(String, (Integer, Integer))]

{-@ data AS = AS [(String, Integer<{\x -> x >= 0}>)] @-}
data AS = AS [(String,Integer)]

{-@ type Posi = {v:Integer | 0 <= v} @-}
{-@ type Posit = {v:Integer | 0 < v} @-}
{-@ type ProperMap = [(String, Posi)] @-}
{-@ type ProperLO = [(String, (Posi, Posi))] @-}
{-@ type ProperMO = [((String, Rational),(Posi, Posi))] @-}

{-}
{-@ fraction:: x:Posi -> Bool -> a:Posit -> {b:Posit| b < a} -> {d:Posi | d <= x} @-}
{-@ fraction:: x:Posi -> Bool -> Posit -> Posit -> Posi @-}
fraction :: Integer -> Bool -> Integer -> Integer -> Integer
-}
{-@ fraction:: x:Posi -> a:Posit -> {b:Posit | b > a} -> {y:Posi | y < x} @-}
fraction :: Integer -> Integer -> Integer -> Integer
fraction x a b = (x * a) `div` b

{-@ modulo:: Posi -> Posit -> b:Posit -> {y:Posi | y < b} @-}
modulo :: Integer -> Integer -> Integer -> Integer
modulo x a b = (x * a) `mod` b


{-@ predicate Pur O U V = if (O == (Just True)) then U < (fst (snd V)) else U == (fst (snd V)) @-}
{-@ predicate Sel O U V = if (O == (Just True)) then U < (snd (snd V)) else U == (snd (snd V)) @-}
{-@ predicate Tes O X L = if (O == (Just True)) then X <= (fst (snd L)) else X <= (fst (snd L))@-}

    {- 
    {-@ inline pur @-} 
{-@ pur :: (Maybe Bool) -> Posi -> ((String, Rational),(Posi,Posi)) -> Bool @-}
pur :: (Maybe Bool) -> Integer -> ((String, Rational),(Integer,Integer)) -> Bool
    case ok of
            (Just True) -> u < (fst (snd v))
            _ -> u == 

{-@ inline sel @-} 
{-@ sel :: Maybe Bool -> Posi -> ((String, Rational),(Posi,Posi)) -> Bool @-}
sel :: Maybe Bool -> Integer -> ((String, Rational),(Integer,Integer)) -> Bool
sel ok u v = if (ok == (Just True)) then u < (snd (snd v))
            else u == (snd (snd v)) 
            {-case ok of
            (Just True) -> u < (snd (snd v))
            _ -> u == (snd (snd v))-}-}
{-
{-@ predicate Cux N L = (fst N == (fst (snd L))) && (snd N == (snd (snd L))) @-}            
{-@ predicate Bux N L = (fst N < (fst (snd L))) && (snd N < (snd (snd L))) @-}
{-@ predicate Aux O N L = if (snd O == (Just True)) then (Bux N L) else (Cux N L) @-}

{-@ fracLO:: l:((String, Rational),(Posi,Posi)) -> ((String, Maybe Bool), (Posi,Posi))<{\ok n -> Aux ok n l}> @-}
fracLO :: ((String, Rational),(Integer, Integer)) -> ((String, Maybe Bool), (Integer, Integer))
fracLO ((pkh, r), (p, s)) = if (a <= 0) || (b <= 0) then ((pkh, Nothing),(p, s))
                            else if (a >= b) then ((pkh, Just False),(p, s))
                                else if (modulo p a b /= 0) then if ((fraction p a b)+1 >= p) then ((pkh, Just False), (p, s))
                                                        else ((pkh, Just True), ((fraction p a b)+1, (fraction s a b)))
                                    else ((pkh, Just True), ((fraction p a b), (fraction s a b)))
        where 
            a = numerator r
            b = denominator r


{-@ process :: String -> ProperMap -> Whatever -> Whateverr -> Posi -> Posi -> Maybe AccountState @-}
process :: String -> [(String, Integer)] -> [(String, (Integer, Integer))] -> [((String, Rational),(Integer, Integer))] -> Integer -> Integer -> Maybe AccountState
process pkh accts lob [] v c = case (lookup' pkh accts) of
                                Nothing -> Nothing
                                (Just v0) -> if (c <= v0) then Just ( (AccountState((pkh, v0 + v - c) : (delete pkh accts)) lob))
                                            else Nothing
process pkh accts lob (((u, r),(p, s)):los) v c = case ok of
                                                    Nothing -> Nothing
                                                    Just False -> process pkh ((u, v' + p):(delete u accts)) lob los (v+s) (c+p) 
                                                    Just True -> process pkh ((u', v' + p'):(delete u accts)) ((u', (p-p', s-s')):lob) los (v+s') (c+p')
    where
        ((u', ok), (p', s')) = fracLO ((u, r),(p, s))
        v' = case (lookup' u accts) of
                Nothing -> 0
                (Just v1) -> v1
-}



data TransferArgs = TransferArgs String String Integer

data LOArgs = LOArgs String Integer Integer

data MOArgs = MOArgs String [((String, Rational),(Integer, Integer))]

--{-@ data WDArgs = WDArgs String Integer<{\x -> x >= 0}>)] @-}
data WDArgs = WDArgs String Integer

data AccountInput =
      Transfer TransferArgs
    | Withdraw WDArgs
    | Deposit WDArgs
    | Open String
    | Close String
    | Offer LOArgs
    | Request MOArgs

--{-@ myPlus :: Posi -> Integer -> Posi @-}
--myPlus :: Integer -> Integer -> Integer
--myPlus a b = a + b


--{t:(Maybe (AccountStateP, Integer))| True}
{-@ transition :: AccountStateP -> c:Integer -> AccountInput -> t:(Maybe (AccountStateP, Integer))@-}
transition :: AccountStateP -> Integer -> AccountInput -> Maybe (AccountStateP, Integer)
transition (AccountStateP accts lob) currV i = case i of

    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just ((AccountStateP ((pkh, 0) : accts) lob), currV)

    (Close pkh) -> case lookup pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just ((AccountStateP (delete pkh accts) lob), currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then
                       Just ((AccountStateP ((pkh, v0 + v) : (delete pkh accts)) lob),
                       (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just ((AccountStateP ((pkh, v0 - v) : (delete pkh accts)) lob),
                             (currV - v))
                                else Nothing

    (Transfer (TransferArgs pkh1 pkh2 v)) -> case ((lookup pkh1 accts),(lookup pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) then
            Just ((AccountStateP ((pkh1, v1 - v) : (delete pkh1 ((pkh2, v2 + v) : (delete pkh2 accts)))) lob), currV)
                                else Nothing

{-
    (Offer (LOArgs pkh buy sell)) -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v) ->  if (sell <= v) then
                       Just ((AccountState  ((pkh, v - sell) : (delete pkh accts)) ((pkh, (buy,sell)):lob) ), currV)
                                else Nothing


    (Request (MOArgs pkh los))
           ->  if checkLO los lob then
                case (process pkh accts (cleanLO los lob) los 0 0) of
                   Nothing -> Nothing
                   (Just ( ( AccountState accts' lob'))) ->
                        Just ( (AccountState accts' lob'), currV)
                else Nothing
-}
    _           -> Nothing -- todo

{-
{-@ prop1 :: ProperState -> AccountInput -> ProperState @-}
prop1 :: ProperState -> AccountInput -> ProperState
prop1 (ProperState a l) i = case transition (AccountState a l) 0 i of
    Just ((AccountState acc lo), c) -> ProperState acc lo
    Nothing -> ProperState [("jij",-1)] [("jij",(-1,-1))]

{-@ prop1 :: AccountStateP -> String -> Posi -> {t:(Maybe (AccountStateP, Integer))| isJust t} @-}
prop1 :: AccountStateP -> String -> Integer -> Maybe (AccountStateP, Integer)
prop1 accS pkh v = transition accS 0 (Withdraw (WDArgs pkh v))

-}

{-@ transition2 :: AccountStateP -> c:Integer -> AccountInput -> t:(Maybe (AccountStateP, Integer))@-}
transition2 :: AccountStateP -> Integer -> AccountInput -> Maybe (AccountStateP, Integer)
transition2 (AccountStateP accts lob) currV i = case i of

    (Open pkh) -> case lookup pkh accts of
        Just _  -> Nothing 
        Nothing ->
            Just ((AccountStateP ((pkh, 0) : accts) lob), currV)

    (Close pkh) -> case lookup pkh accts of
        Nothing -> Nothing
        (Just v0) -> if (v0 == 0) then
            Just ((AccountStateP (delete pkh accts) lob), currV)
                    else Nothing
                   
    (Deposit (WDArgs pkh v))
           -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if v >= 0 then
                       Just ((AccountStateP ((pkh, v0 + v) : (delete pkh accts)) lob),
                       (currV + v))
                            else Nothing

    (Withdraw (WDArgs pkh v))
           -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v0) -> if (v <= v0) then
                       Just ((AccountStateP ((pkh, v0 - v) : (delete pkh accts)) lob),
                             (currV - v))
                                else Nothing

    (Transfer (TransferArgs pkh1 pkh2 v)) -> case ((lookup pkh1 accts),(lookup pkh2 accts)) of
        (Nothing,_) -> Nothing
        (_,Nothing) -> Nothing
        (Just v1, Just v2) -> if (v <= v1) && (v >= 0) then
            Just ((AccountStateP ((pkh1, v1 - v) : (delete pkh1 ((pkh2, v2 + v) : (delete pkh2 accts)))) lob), currV)
                                else Nothing

{-
    (Offer (LOArgs pkh buy sell)) -> case (lookup pkh accts) of
                   Nothing -> Nothing
                   (Just v) ->  if (sell <= v) then
                       Just ((AccountState  ((pkh, v - sell) : (delete pkh accts)) ((pkh, (buy,sell)):lob) ), currV)
                                else Nothing


    (Request (MOArgs pkh los))
           ->  if checkLO los lob then
                case (process pkh accts (cleanLO los lob) los 0 0) of
                   Nothing -> Nothing
                   (Just ( ( AccountState accts' lob'))) ->
                        Just ( (AccountState accts' lob'), currV)
                else Nothing
-}
    _           -> Nothing -- todo

{-@ initial :: AccountStateP @-}
initial :: AccountStateP
initial = AccountStateP [] []