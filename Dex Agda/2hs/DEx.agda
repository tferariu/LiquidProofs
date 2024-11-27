module DEx where

open import Haskell.Prelude

variable
  k v : Set

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Nat
TokenName = Nat

PubKeyHash = Nat --no longer string because of equality issues


Value = Integer
--List (CurrencySymbol × (List (TokenName × Integer))) 
{-
record Value : Set where
    field
        val : Integer
        ac  : AssetClass
open Rational public
-}

AssetClass = Nat

{-
--CurrencySymbol × TokenName

assetClass : CurrencySymbol -> TokenName -> AssetClass
assetClass cs tn = cs , tn
-}


record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r

checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

Cmap = List ((Rational × PubKeyHash) × Integer)

record Label : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
    --cmap2 : Cmap --List ((Rational × PubKeyHash) × Integer)
open Label public
{-# COMPILE AGDA2HS Label #-}

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b

lookup' : {{Eq k}} -> k -> List (k × v) -> Maybe v
lookup' x [] = Nothing
lookup' x ( ( x' , y ) ∷ xs ) = if (x == x')
  then Just y
  else lookup' x xs

insert' : {{Ord k}} -> k -> Integer -> List (k × Integer) -> List (k × Integer)
insert' key val [] = ( key , val ) ∷ []
insert' key val ( ( k , v ) ∷ xs ) = if (key < k)
  then ( key , val ) ∷ ( ( k , v ) ∷ xs )
  else if (key == k)
       then (key , (v + val)) ∷ xs
       else (k , v) ∷ (insert' key val xs)

reduce' : {{Ord k}} -> k -> Integer -> List (k × Integer) -> List (k × Integer)
reduce' key val [] = ( key , val ) ∷ []
reduce' key val ( ( k , v ) ∷ xs ) = if (key < k)
  then ( key , val ) ∷ ( ( k , v ) ∷ xs )
  else if (key == k)
       then (key , (v - val)) ∷ xs
       else (k , v) ∷ (reduce' key val xs)

delete' : {{Eq k}} -> k -> List (k × v) -> List (k × v)
delete' x [] = []
delete' x ( ( x' , y ) ∷ xs ) = if (x == x')
  then xs
  else delete' x xs


{-
singleton : CurrencySymbol -> TokenName -> Integer -> Value
singleton cs tn v = (cs , ( (tn , v)  ∷ [])) ∷ []
-}


instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

  iOrdRational : Ord Rational
  iOrdRational = ordFromLessThan ltRational


eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel
{--}

record ScriptContext : Set where
    field
        inputVal    : Value
        outputVal   : Value
        outputLabel : Label
        payTo       : PubKeyHash
        payAmt      : Value
        buyTo       : PubKeyHash
        buyAmt      : Value
        signature   : PubKeyHash
        continues   : Bool
open ScriptContext public


checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx


data Input : Set where
  Update   : Integer -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}

newLabel : ScriptContext -> Label
newLabel ctx = outputLabel ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = continues ctx

ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)

checkPayment : Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt st ctx = payTo ctx == owner st &&
                              ratioCompare amt (payAmt ctx) (ratio st)



checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = buyTo ctx == pkh &&
                             buyAmt ctx == amt

checkClose : Params -> Label -> ScriptContext -> Bool
checkClose par st ctx = payTo ctx == owner st &&
                        payAmt ctx == oldValue ctx


agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par st red ctx = case red of λ where
  (Update amt r) -> checkSigned (owner st) ctx &&
                    checkRational r &&
                    newValue ctx == amt &&
                    newLabel ctx == record {ratio = r ; owner = owner st} &&
                    continuing ctx
  (Exchange amt pkh) -> oldValue ctx == newValue ctx + amt &&
                        newLabel ctx == st &&
                        checkPayment par amt st ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx
  Close -> not (continuing ctx) &&
           checkSigned (owner st) ctx --checkClose par st ctx
           

{-case red of λ where
  (Offer pkh v b r) -> checkSigned pkh ctx && v > 0 &&
                       (numerator r * denominator r) > 0 &&
                       checkOffer pkh v b r dat ctx
                       
  (Request pkh b map) -> True

{-
(checkSigned pkh)                                                         &&
(ok (resp map cs tn))                                                     &&
(checkReqD cs tn st map)                                                  &&
(checkPayments (pMap (resp map cs tn)) (cOut (resp map cs tn)))           &&
( (txOutValue ownInput) <> singleton cs tn (tOut (resp map cs tn)) == (txOutValue ownOutput) )


    processReq :: Cmap -> CurrencySymbol -> TokenName -> State -> Response
    processReq map cs tn state
        | ac == c1 state = (preProc map (cmap1 state) def) {cOut = c2 state}
        | ac == c2 state = (preProc map (cmap2 state) def) {cOut = c1 state}
        | otherwise = def {ok = False}
    		where
    		ac  = assetClass cs tn
    		def = Response
    		      { ok   = True
    		      , tOut = 0 
    	 	      , cOut = ac 
    		      , pMap = [] }
    	      
    preProc :: [((Rational,PaymentPubKeyHash),Integer)] -> [((Rational,PaymentPubKeyHash),Integer)] -> Response -> Response
    preProc (((r1,pkh1),amt1):xs) (((r2,pkh2),amt2):ys) resp 
    	| (r1,pkh1) == (r2,pkh2) = if amt1 == amt2 then preProc xs ys resp
    	                            else if amt1 > amt2 then resp {ok = False}
    	                                 else preProc xs ys Response
    		 					     {  ok   = True
    							      , tOut = tOut resp - amt2 + amt1
    	 						      , cOut = cOut resp
    							      , pMap = insert' pkh1 (compute r2 (amt2 - amt1)) (pMap resp) }
    	| (r1,pkh1) > (r2,pkh2)  = preProc (((r1,pkh1),amt1):xs) ys Response
    		 					     	    { ok   = True
    							  	    , tOut = tOut resp - amt2
    	 						            , cOut = cOut resp
    								    , pMap = insert' pkh2 (compute r2 amt2) (pMap resp ) }
  	| (r1,pkh1) < (r2,pkh2)  = resp {ok = False}	
    preProc [] (((r2,pkh2),amt2):ys) resp = preProc [] ys Response
    							    { ok   = True
    						  	    , tOut = tOut resp - amt2
    	 					            , cOut = cOut resp
    						  	    , pMap = insert' pkh2 (compute r2 amt2) (pMap resp) }
    preProc (x:xs) [] resp = resp {ok = False}
    preProc [] [] resp = resp	           
  
    resp :: [((Rational,PaymentPubKeyHash),Integer)] -> CurrencySymbol -> TokenName -> Response
    resp map cs tn = processReq map cs tn st    
    
    checkReqD ::  CurrencySymbol -> TokenName -> State -> [((Rational,PaymentPubKeyHash),Integer)] -> Bool
    checkReqD cs tn st map
        | ac == c1 st = outputDatum == st {cmap1 = map} 
        | ac == c2 st = outputDatum == st {cmap2 = map}                                
        | otherwise   = False
        	where
        	ac = assetClass cs tn
		
    count :: [TxOut] -> AssetClass -> Integer -> Integer
    count [] ac c = c
    count (o:os) ac c = count os ac (c+ (getVal o ac))
    
    paymentVal :: PaymentPubKeyHash -> AssetClass -> Integer
    paymentVal pkh ac = case filter (\i -> (txOutAddress i == (Addrs.pubKeyHashAddress (unPaymentPubKeyHash pkh)))) (txInfoOutputs info) of
        os -> count os ac 0 
        
    checkPayments :: [(PaymentPubKeyHash,Integer)] -> AssetClass -> Bool
    checkPayments [] ac = True
    checkPayments ((pkh,val):xs) ac = paymentVal pkh ac == val && checkPayments xs ac
    



-}

  (Cancel pkh v b r) -> checkSigned pkh ctx &&
                        checkCancel pkh v b r dat ctx 

-}
{-
query : PubKeyHash -> List PubKeyHash -> Bool
query pkh [] = False
query pkh (x ∷ l') = (x == pkh) || query pkh l'

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}



checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx

expired : Deadline -> ScriptContext -> Bool
expired d ctx = (time ctx) > d



geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
open Params public


{-# COMPILE AGDA2HS Params #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx = case dat of λ where

  Holding -> case red of λ where

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && gt v emptyValue && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == [] )
    (Add _) -> False
    Pay -> False
    Cancel -> False 

  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs )

    Pay -> (lengthNat sigs) >= (nr param) && (case (newLabel ctx) of λ where
      Holding -> checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v)
      (Collecting _ _ _ _) -> False )
      
    Cancel -> newValue ctx == oldValue ctx && (case (newLabel ctx) of λ where
      Holding -> expired d ctx
      (Collecting _ _ _ _) -> False)
  

{-# COMPILE AGDA2HS agdaValidator #-}


-}


{-
appendSubValue : List (TokenName × Integer) -> List (TokenName × Integer) -> List (TokenName × Integer)
appendSubValue [] l = l
appendSubValue ((x , y) ∷ zs) l = insert' x y (appendSubValue zs l)

insertSubValue : CurrencySymbol -> List (TokenName × Integer) -> Value -> Value
insertSubValue key val [] =  ( key , val ) ∷ []
insertSubValue key val ( ( k , v ) ∷ xs ) = if (key == k)
       then (key , (appendSubValue v val)) ∷ xs
       else (k , v) ∷ (insertSubValue key val xs)

appendValue : Value -> Value -> Value
appendValue [] v = v
appendValue ((x , y) ∷ zs) v = insertSubValue x y (appendValue zs v)

--  iSemigroupValue : Semigroup Value
--  iSemigroupValue ._<>_ = appendValue

-}


{-
  = if ( cs , tn ) == c1 st
       then (case (lookup' (r , pkh) (cmap1 st)) of λ where
            Nothing -> False
            (Just val') -> val' >= val)
       else if ( cs , tn ) == c2 st
            then (case (lookup' (r , pkh) (cmap2 st)) of λ where
                 Nothing -> False
                 (Just val') -> val' >= val)
            else False -}



{-
  = if ( cs , tn ) == c1 st
       then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ;
            cmap1 = insert' (r , pkh) val (cmap1 st) ; cmap2 = cmap2 st}
       else if ( cs , tn ) == c2 st
            then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ; cmap1 = cmap1 st ;
            cmap2 = insert' (r , pkh) val (cmap2 st) }
            else False -}

{-
  = if ( cs , tn ) == c1 st
       then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ;
            cmap1 = reduce' (r , pkh) val (cmap1 st) ; cmap2 = cmap2 st}
       else if ( cs , tn ) == c2 st
            then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ; cmap1 = cmap1 st ;
            cmap2 = reduce' (r , pkh) val (cmap2 st) }
            else False -}
