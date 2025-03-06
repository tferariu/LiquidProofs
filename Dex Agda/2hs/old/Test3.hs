module Test3 where

type PubKeyHash = String

data Datum = Holding
           | Collecting Integer PubKeyHash Integer [PubKeyHash]

data Redeemer = Propose Integer PubKeyHash Integer
              | Add PubKeyHash
              | Pay
              | Cancel

(∈) :: PubKeyHash -> [PubKeyHash] -> Bool
pkh ∈ [] = False
pkh ∈ (x : l') = x == pkh || (pkh ∈ l')

agdaValidator :: State -> Transition -> State -> Inputs
        -> Outputs -> [PubKeyHash] -> OtherStuff -> Bool
agdaValidator s t s' i o sigs stuff
  = case t of
        Add pkh -> pkh ∈ sigs
        _ -> False

{-# INLINABLE mkValidator #-}
mkValidator :: [PubKeyHash] -> Datum -> Redeemer -> ScriptContext -> Bool
mkValidator sigs dat red ctx =
    traceIfFalse "token missing from input" (getVal ownInput (tToken dat) == 1)    &&
    traceIfFalse "token missing from output" (getVal ownOutput (tToken dat) == 1)  &&
    traceIfFalse "not properly signed" (checkSigned red)                           &&
    traceIfFalse "failed validation" (agdaValidator s red s' i o sigs stuff)
  where
    checkSigned :: Redeemer -> Bool
    checkSigned red = case red of
          Add pkh -> txSignedBy (scriptContextTxInfo ctx) pkh
          Propose _ pkh _ -> txSignedBy (scriptContextTxInfo ctx) pkh
          _ -> True

    ownInput :: TxOut
    ownInput = case findOwnInput ctx of
        Nothing -> traceError "state input missing"
        Just i  -> txInInfoResolved i

    ownOutput :: TxOut
    ownOutput = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one SM output"

    outputDatum :: State
    outputDatum = case txOutDatum ownOutput of
        NoOutputDatum-> traceError "nt"
        OutputDatumHash dh -> case smDatum $ findDatum dh info of
            Nothing -> traceError "hs"
            Just d  -> d
        OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)
        _ -> traceError "?"
