module Validators.AccountSim where

import Lib (Address, AssetClass, PubKeyHash, TxOutRef)
import Value (Value, emptyValue, geq)

type AccMap = [(PubKeyHash, Value)]

type Label = (AssetClass, AccMap)

data Input = Open PubKeyHash
           | Close PubKeyHash
           | Withdraw PubKeyHash Value
           | Deposit PubKeyHash Value
           | Transfer PubKeyHash PubKeyHash Value
           | Cleanup

insert :: PubKeyHash -> Value -> AccMap -> AccMap
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs)
  = if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

delete :: PubKeyHash -> AccMap -> AccMap
delete pkh [] = []
delete pkh ((x, y) : xs)
  = if pkh == x then xs else (x, y) : delete pkh xs

checkMembership :: Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

checkEmpty :: Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

checkWithdraw ::
              AssetClass ->
                Maybe Value ->
                  PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val lab ctx
  = geq val emptyValue &&
      geq v val && newDatum ctx == (tok, insert pkh (v - val) lab)

checkDeposit ::
             AssetClass ->
               Maybe Value ->
                 PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val lab ctx
  = geq val emptyValue &&
      newDatum ctx == (tok, insert pkh (v + val) lab)

checkTransfer ::
              AssetClass ->
                Maybe Value ->
                  Maybe Value ->
                    PubKeyHash ->
                      PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val lab ctx
  = geq val emptyValue &&
      geq vF val &&
        from /= to &&
          newDatum ctx ==
            (tok, insert from (vF - val) (insert to (vT + val) lab))

agdaValidator :: Label -> Input -> ScriptContext -> Bool
agdaValidator (tok, lab) inp ctx
  = checkTokenIn tok ctx &&
      case inp of
          Open pkh -> checkTokenOut tok ctx &&
                        continuing ctx &&
                          checkSigned pkh ctx &&
                            not (checkMembership (lookup pkh lab)) &&
                              newDatum ctx == (tok, insert pkh emptyValue lab) &&
                                newValue ctx == oldValue ctx
          Close pkh -> checkTokenOut tok ctx &&
                         continuing ctx &&
                           checkSigned pkh ctx &&
                             checkEmpty (lookup pkh lab) &&
                               newDatum ctx == (tok, delete pkh lab) &&
                                 newValue ctx == oldValue ctx
          Withdraw pkh val -> checkTokenOut tok ctx &&
                                continuing ctx &&
                                  checkSigned pkh ctx &&
                                    checkWithdraw tok (lookup pkh lab) pkh val lab ctx &&
                                      newValue ctx + val == oldValue ctx
          Deposit pkh val -> checkTokenOut tok ctx &&
                               continuing ctx &&
                                 checkSigned pkh ctx &&
                                   checkDeposit tok (lookup pkh lab) pkh val lab ctx &&
                                     newValue ctx == oldValue ctx + val
          Transfer from to val -> checkTokenOut tok ctx &&
                                    continuing ctx &&
                                      checkSigned from ctx &&
                                        checkTransfer tok (lookup from lab) (lookup to lab) from to
                                          val
                                          lab
                                          ctx
                                          && newValue ctx == oldValue ctx
          Cleanup -> checkTokenBurned tok ctx &&
                       not (checkTokenOut tok ctx) && not (continuing ctx) && lab == []

checkDatum :: Address -> ScriptContext -> Bool
checkDatum addr ctx
  = case newDatum ctx of
        (tok, map) -> ownAssetClass ctx == tok && map == []

checkValue :: Address -> ScriptContext -> Bool
checkValue addr ctx
  = newValue ctx == emptyValue &&
      checkTokenOut (ownAssetClass ctx) ctx

isInitial :: Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx
  = consumes oref ctx && checkDatum addr ctx && checkValue addr ctx

agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial addr oref ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

