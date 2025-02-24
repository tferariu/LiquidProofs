module AccountSim where

type Label = [(PubKeyHash, Value)]

data Input = Open PubKeyHash
           | Close PubKeyHash
           | Withdraw PubKeyHash Value
           | Deposit PubKeyHash Value
           | Transfer PubKeyHash PubKeyHash Value

insert :: PubKeyHash -> Value -> Label -> Label
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs)
  = if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

delete :: PubKeyHash -> Label -> Label
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
              Maybe Value ->
                PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkWithdraw Nothing _ _ _ _ = False
checkWithdraw (Just v) pkh val lab ctx
  = geq val emptyValue &&
      geq v val && newLabel ctx == insert pkh (v - val) lab

checkDeposit ::
             Maybe Value ->
               PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkDeposit Nothing _ _ _ _ = False
checkDeposit (Just v) pkh val lab ctx
  = geq val emptyValue && newLabel ctx == insert pkh (v + val) lab

checkTransfer ::
              Maybe Value ->
                Maybe Value ->
                  PubKeyHash -> PubKeyHash -> Value -> Label -> ScriptContext -> Bool
checkTransfer Nothing _ _ _ _ _ _ = False
checkTransfer (Just vF) Nothing _ _ _ _ _ = False
checkTransfer (Just vF) (Just vT) from to val lab ctx
  = geq vF val &&
      geq val 0 &&
        from /= to &&
          newLabel ctx == insert from (vF - val) (insert to (vT + val) lab)

checkPayment :: PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx

agdaValidator :: Label -> Input -> ScriptContext -> Bool
agdaValidator lab inp ctx
  = case inp of
        Open pkh -> checkSigned pkh ctx &&
                      not (checkMembership (lookup pkh lab)) &&
                        newLabel ctx == insert pkh 0 lab && newValue ctx == oldValue ctx
        Close pkh -> checkSigned pkh ctx &&
                       checkEmpty (lookup pkh lab) &&
                         newLabel ctx == delete pkh lab && newValue ctx == oldValue ctx
        Withdraw pkh val -> checkSigned pkh ctx &&
                              checkWithdraw (lookup pkh lab) pkh val lab ctx &&
                                newValue ctx == oldValue ctx - val && checkPayment pkh val ctx
        Deposit pkh val -> checkSigned pkh ctx &&
                             checkDeposit (lookup pkh lab) pkh val lab ctx &&
                               newValue ctx == oldValue ctx + val
        Transfer from to val -> checkSigned from ctx &&
                                  checkTransfer (lookup from lab) (lookup to lab) from to val lab
                                    ctx
                                    && newValue ctx == oldValue ctx

