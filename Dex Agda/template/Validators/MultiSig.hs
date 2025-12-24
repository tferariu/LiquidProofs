module Validators.MultiSig where

import Lib (Address, AssetClass, POSIXTime, PubKeyHash, TokenName, TxOutRef)
import Numeric.Natural (Natural)
import Value (2xMinValue, Value, geq, lovelaces, minValue)

data Info = Holding
          | Collecting Value PubKeyHash Integer [PubKeyHash]

type Label = (AssetClass, Info)

data Input = Propose Value PubKeyHash Integer
           | Add PubKeyHash
           | Pay
           | Cancel
           | Close

data Params = Params{authSigs :: [PubKeyHash], nr :: Natural,
                     maxWait :: Integer}

query :: PubKeyHash -> [PubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || query pkh l'

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if pkh == x then x : l' else x : insert pkh l'

expired :: Integer -> ScriptContext -> Bool
expired d ctx = before (POSIXTime d) (validRange ctx)

notTooLate :: Params -> Integer -> ScriptContext -> Bool
notTooLate par d ctx
  = before (POSIXTime (d - maxWait par)) (validRange ctx)

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case (checkTokenOut tok ctx, lab, red) of
          (True, Holding, Propose v pkh d) -> newValue ctx == oldValue ctx &&
                                                geq (oldValue ctx) v &&
                                                  lovelaces v >= lovelaces minValue &&
                                                    notTooLate param d ctx &&
                                                      continuing ctx &&
                                                        case newDatum ctx of
                                                            (tok', Holding) -> False
                                                            (tok',
                                                             Collecting v' pkh' d' sigs') -> v == v'
                                                                                               &&
                                                                                               pkh
                                                                                                 ==
                                                                                                 pkh'
                                                                                                 &&
                                                                                                 d ==
                                                                                                   d'
                                                                                                   &&
                                                                                                   sigs'
                                                                                                     ==
                                                                                                     []
                                                                                                     &&
                                                                                                     tok
                                                                                                       ==
                                                                                                       tok'
          (True, Collecting v pkh d sigs, Add sig) -> newValue ctx ==
                                                        oldValue ctx
                                                        &&
                                                        checkSigned sig ctx &&
                                                          query sig (authSigs param) &&
                                                            continuing ctx &&
                                                              case newDatum ctx of
                                                                  (tok', Holding) -> False
                                                                  (tok',
                                                                   Collecting v' pkh' d'
                                                                     sigs') -> v == v' &&
                                                                                 pkh == pkh' &&
                                                                                   d == d' &&
                                                                                     sigs' ==
                                                                                       insert sig
                                                                                         sigs
                                                                                       &&
                                                                                       tok == tok'
          (True, Collecting v pkh d sigs, Pay) -> lengthNat sigs >= nr param
                                                    &&
                                                    continuing ctx &&
                                                      case newDatum ctx of
                                                          (tok', Holding) -> checkPayment pkh v ctx
                                                                               &&
                                                                               oldValue ctx ==
                                                                                 newValue ctx + v
                                                                                 && tok == tok'
                                                          (tok',
                                                           Collecting v' pkh' d' sigs') -> False
          (True, Collecting v pkh d sigs, Cancel) -> newValue ctx ==
                                                       oldValue ctx
                                                       &&
                                                       continuing ctx &&
                                                         case newDatum ctx of
                                                             (tok', Holding) -> expired d ctx &&
                                                                                  tok == tok'
                                                             (tok',
                                                              Collecting v' pkh' d' sigs') -> False
          (False, Holding, Close) -> lovelaces 2xMinValue >
                                       lovelaces (oldValue ctx)
                                       && not (continuing ctx) && checkTokenBurned tok ctx
          _ -> False

checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx
  = case newDatumAddr addr ctx of
        (tok, Holding) -> ownAssetClass tn ctx == tok
        (tok, Collecting _ _ _ _) -> False

checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx
  = lovelaces 2xMinValue < lovelaces (newValueAddr addr ctx) &&
      checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

notIn :: PubKeyHash -> [PubKeyHash] -> Bool
notIn x [] = True
notIn x (y : ys) = if x == y then False else notIn x ys

noDups :: [PubKeyHash] -> Bool
noDups [] = True
noDups (x : xs) = notIn x xs && noDups xs

checkParams :: Params -> Bool
checkParams (Params authSigs nr maxWait)
  = noDups authSigs && lengthNat authSigs >= nr && maxWait > 0

isInitial ::
          Params -> Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial par addr oref tn ctx
  = consumes oref ctx &&
      checkDatum addr tn ctx && checkValue addr tn ctx && checkParams par

agdaPolicy ::
           Params ->
             Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy par addr oref tn _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial par addr oref tn ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

