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
            height                  |-> tip_block.height + 1,
            txs                     |-> txPool
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
    
        \* Verify the block's header.
        if VerifyBlockHeader(proposed_block, tip_block) then
            \* Verify the block's transactions.
            if VerifyBlockTransactions(proposed_block.txs) then
                  \* Update the compact state (Merkle roots) accordingly.
                  noteCommitmentRoot := ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs);
                  nullifierRoot := ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs);
                  \* Update the blockchain's tip block.
                  tip_block := [height |-> proposed_block.height, transactions |-> proposed_block.txs];
            end if;
        end if;
        \* Regardless of validity, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f6539c5" /\ chksum(tla) = "e3a705b7")
CONSTANT defaultInitValue
VARIABLES pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
          proposed_block, tx_, actions, nullifier, commitment

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
                                    height                  |-> tip_block.height + 1,
                                    txs                     |-> txPool
                                ]
           /\ txPool' = {}
           /\ pc' = [pc EXCEPT !["Producer"] = "Done"]
           /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, tx_, 
                           actions, nullifier, commitment >>

Producer == Produce

Verify == /\ pc["Node"] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ IF VerifyBlockTransactions(proposed_block.txs)
                           THEN /\ noteCommitmentRoot' = ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs)
                                /\ nullifierRoot' = ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs)
                                /\ tip_block' = [height |-> proposed_block.height, transactions |-> proposed_block.txs]
                           ELSE /\ TRUE
                                /\ UNCHANGED << noteCommitmentRoot, 
                                                nullifierRoot, tip_block >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, 
                                     tip_block >>
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
