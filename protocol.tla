---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, definitions

(*--algorithm protocol

variables
    \* A compact zk-SNARK proof that summarizes the Merkle tree root of the current note commitments.
    noteCommitmentRoot = <<>>;
    \* A compact zk-SNARK proof that summarizes the Merkle tree root of the current nullifiers.
    nullifierRoot = <<>>;
    \* The blockchain last accepted block.
    tip_block = [height |-> 1, transactions |-> <<>>];
    \* Transaction pool for producers to build blocks.
    txPool = {};
    \* The proposed block from a miner.
    proposed_block;

define
    \* The height of the blockchain always increases
    HeightAlwaysIncreases == [][tip_block'.height > tip_block.height]_tip_block

    \* Transactions in the transaction pool are eventually processed
    TransactionsEventuallyProcessed ==
        (Cardinality(txPool) > 0) => <> (Cardinality(txPool) = 0)

    \* For each transaction in the transaction pool, the nullifier is unique
    NoDoubleSpending ==
        \A tx \in txPool :
            \A action1, action2 \in tx.actions :
                action1 /= action2 => action1.nullifier /= action2.nullifier
end define;

\* User process: User creates actions and a proof, use that to build a transaction and add it to the pool.
fair process User = "User"
variables 
    tx_,
    actions,
    nullifier,
    commitment;
begin
    CreateTx:
        \* Wait until the transaction pool is empty.
        await txPool = {};
        (* Prepare the transaction actions: generate a new nullifier and commitment (each 32 bytes),
        along with a fixed value and a receiver. *)
        actions :=
        {[
            nullifier   |-> RandomBytes(32),
            commitment  |-> RandomBytes(32),
            value       |-> 10,
            receiver    |-> "receiver"
        ]};
        \* Create a new transaction with the actions and a zk-SNARK proof and add it to the pool.
        txPool :=
        {[
            actions |-> actions,
            proof   |-> GenerateZKProof(actions)
        ]};
end process;

\* Producer process: assembles transactions into a block and computes updated state commitments and nullifiers.
fair process Producer = "Producer"
begin
    Produce:
        \* Wait until there is at least one transaction in the pool.
        await Cardinality(txPool) > 0;
        \* Create a new block with an incremented height and the transactions from the pool.
        proposed_block :=
        [
            height  |-> tip_block.height + 1,
            txs     |-> txPool
        ];
        \* Clear the transaction pool after block creation.
        txPool := {};
end process;

\* Node process: verifies the proposed block and updates the state.
fair process Node = "Node"
begin
    Verify:
        \* Wait for a proposed block.
        await proposed_block # defaultInitValue;
        
        \* Panics if the proposed block is invalid.
        assert VerifyBlockHeader(proposed_block, tip_block) = TRUE;
        assert VerifyBlockTransactions(proposed_block.txs) = TRUE;

        \* For each transaction in the proposed block.
        with tx \in proposed_block.txs do
            \* Verify the transaction zk-SNARK proof, panick if invalid.
            assert VerifyZKProof(tx.proof, noteCommitmentRoot, nullifierRoot) = TRUE;
            \* Update the note commitment and nullifier roots.
            noteCommitmentRoot := ComputeNewNoteRoot(noteCommitmentRoot, tx);
            nullifierRoot := ComputeNewNullifierRoot(nullifierRoot, tx);
        end with;
        \* Update the blockchain's tip block.
        tip_block := [height |-> proposed_block.height, transactions |-> proposed_block.txs];
        \* Regardless of validity, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "29f1a93a" /\ chksum(tla) = "5b0dd1a1")
CONSTANT defaultInitValue
VARIABLES pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
          proposed_block

(* define statement *)
HeightAlwaysIncreases == [][tip_block'.height > tip_block.height]_tip_block


TransactionsEventuallyProcessed ==
    (Cardinality(txPool) > 0) => <> (Cardinality(txPool) = 0)


NoDoubleSpending ==
    \A tx \in txPool :
        \A action1, action2 \in tx.actions :
            action1 /= action2 => action1.nullifier /= action2.nullifier

VARIABLES tx_, actions, nullifier, commitment

vars == << pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
           proposed_block, tx_, actions, nullifier, commitment >>

ProcSet == {"User"} \cup {"Producer"} \cup {"Node"}

Init == (* Global variables *)
        /\ noteCommitmentRoot = <<>>
        /\ nullifierRoot = <<>>
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = defaultInitValue
        /\ actions = defaultInitValue
        /\ nullifier = defaultInitValue
        /\ commitment = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "User" -> "CreateTx"
                                        [] self = "Producer" -> "Produce"
                                        [] self = "Node" -> "Verify"]

CreateTx == /\ pc["User"] = "CreateTx"
            /\ txPool = {}
            /\ actions' = {[
                              nullifier   |-> RandomBytes(32),
                              commitment  |-> RandomBytes(32),
                              value       |-> 10,
                              receiver    |-> "receiver"
                          ]}
            /\ txPool' = {[
                             actions |-> actions',
                             proof   |-> GenerateZKProof(actions')
                         ]}
            /\ pc' = [pc EXCEPT !["User"] = "Done"]
            /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, 
                            proposed_block, tx_, nullifier, commitment >>

User == CreateTx

Produce == /\ pc["Producer"] = "Produce"
           /\ Cardinality(txPool) > 0
           /\ proposed_block' = [
                                    height  |-> tip_block.height + 1,
                                    txs     |-> txPool
                                ]
           /\ txPool' = {}
           /\ pc' = [pc EXCEPT !["Producer"] = "Done"]
           /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, tx_, 
                           actions, nullifier, commitment >>

Producer == Produce

Verify == /\ pc["Node"] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ Assert(VerifyBlockHeader(proposed_block, tip_block) = TRUE, 
                    "Failure of assertion at line 85, column 9.")
          /\ Assert(VerifyBlockTransactions(proposed_block.txs) = TRUE, 
                    "Failure of assertion at line 86, column 9.")
          /\ \E tx \in proposed_block.txs:
               /\ Assert(VerifyZKProof(tx.proof, noteCommitmentRoot, nullifierRoot) = TRUE, 
                         "Failure of assertion at line 91, column 13.")
               /\ noteCommitmentRoot' = ComputeNewNoteRoot(noteCommitmentRoot, tx)
               /\ nullifierRoot' = ComputeNewNullifierRoot(nullifierRoot, tx)
          /\ tip_block' = [height |-> proposed_block.height, transactions |-> proposed_block.txs]
          /\ proposed_block' = defaultInitValue
          /\ pc' = [pc EXCEPT !["Node"] = "Done"]
          /\ UNCHANGED << txPool, tx_, actions, nullifier, commitment >>

Node == Verify

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == User \/ Producer \/ Node
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(User)
        /\ WF_vars(Producer)
        /\ WF_vars(Node)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
