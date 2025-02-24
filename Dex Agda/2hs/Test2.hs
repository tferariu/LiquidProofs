module Test2 where

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

txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy info pkh = pkh ∈ txInfoSignatories info

agdaValidator ::
              [PubKeyHash] -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator sigs dat red ctx
  = case red of
        Add pkh -> txSignedBy (scriptContextTxInfo ctx) pkh && (pkh ∈ sigs)
        _ -> False

