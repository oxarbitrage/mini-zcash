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

\* Producer process: assembles transactions into a block and computes updated state commitments and nullifiers.
\* TODO: Miners/Producers may be doing lot of stuff at low latency, maybe move proofs to the user side.
fair process Producer = "Producer"
begin
    Produce:
        \* Wait until there is at least one transaction in the pool.
        await Cardinality(txPool) > 0;
        (* Create a new block with:
            - an incremented height,
            - the transactions from the pool,
            - a new note commitment root computed from the current noteCommitmentRoot and the transactions,
            - and a new nullifier root computed from the current nullifierRoot and the transactions. *)
        proposed_block :=
        [
            height                  |-> tip_block.height + 1,
            txs                     |-> txPool,
            newNoteCommitmentRoot   |-> GenerateZKProof(txPool, noteCommitmentRoot),
            newNullifierRoot        |-> GenerateZKProof(txPool, nullifierRoot)
        ];
        \* Clear the transaction pool after block creation.
        txPool := {};
end process;

\* User process: each user creates a transaction and adds it to the transaction pool.
fair process User = "User"
variables 
    tx_,
    actions;
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
        \* Generate a transaction with a zk-SNARK proof based on the current noteCommitmentRoot.
        tx_ := OrchardTransaction(actions, GenerateZKProof(actions, noteCommitmentRoot));
        \* Add the transaction to the pool.
        txPool := {tx_};
end process;

\* Node process: verifies the proposed block and updates the state.
fair process Node = "Node"
begin
    Verify:
        \* Wait for a proposed block.
        await proposed_block # defaultInitValue;
    
        if VerifyBlockHeader(proposed_block, tip_block) then
            \* Verify that the block's updated state commitments are correct by re-computing them ...
            if ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs)
                = proposed_block.newNoteCommitmentRoot
                /\ ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs)
                = proposed_block.newNullifierRoot then
                  \* Update the compact state (Merkle roots) accordingly.
                  noteCommitmentRoot := proposed_block.newNoteCommitmentRoot;
                  nullifierRoot := proposed_block.newNullifierRoot;
                  \* Update the blockchain's tip block.
                  tip_block := [height |-> proposed_block.height, transactions |-> proposed_block.txs];
            end if;
        end if;
        \* Regardless of validity, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a81a89f8" /\ chksum(tla) = "784e85d5")
CONSTANT defaultInitValue
VARIABLES pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
          proposed_block, tx_, actions

vars == << pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
           proposed_block, tx_, actions >>

ProcSet == {"Producer"} \cup {"User"} \cup {"Node"}

Init == (* Global variables *)
        /\ noteCommitmentRoot = <<>>
        /\ nullifierRoot = <<>>
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = defaultInitValue
        /\ actions = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "Producer" -> "Produce"
                                        [] self = "User" -> "CreateTx"
                                        [] self = "Node" -> "Verify"]

Produce == /\ pc["Producer"] = "Produce"
           /\ Cardinality(txPool) > 0
           /\ proposed_block' = [
                                    height                  |-> tip_block.height + 1,
                                    txs                     |-> txPool,
                                    newNoteCommitmentRoot   |-> GenerateZKProof(txPool, noteCommitmentRoot),
                                    newNullifierRoot        |-> GenerateZKProof(txPool, nullifierRoot)
                                ]
           /\ txPool' = {}
           /\ pc' = [pc EXCEPT !["Producer"] = "Done"]
           /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, tx_, 
                           actions >>

Producer == Produce

CreateTx == /\ pc["User"] = "CreateTx"
            /\ txPool = {}
            /\ actions' = {[
                              nullifier   |-> RandomBytes(32),
                              commitment  |-> RandomBytes(32),
                              value       |-> 10,
                              receiver    |-> "receiver"
                          ]}
            /\ tx_' = OrchardTransaction(actions', GenerateZKProof(actions', noteCommitmentRoot))
            /\ txPool' = {tx_'}
            /\ pc' = [pc EXCEPT !["User"] = "Done"]
            /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, 
                            proposed_block >>

User == CreateTx

Verify == /\ pc["Node"] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ IF ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs)
                            = proposed_block.newNoteCommitmentRoot
                            /\ ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs)
                            = proposed_block.newNullifierRoot
                           THEN /\ noteCommitmentRoot' = proposed_block.newNoteCommitmentRoot
                                /\ nullifierRoot' = proposed_block.newNullifierRoot
                                /\ tip_block' = [height |-> proposed_block.height, transactions |-> proposed_block.txs]
                           ELSE /\ TRUE
                                /\ UNCHANGED << noteCommitmentRoot, 
                                                nullifierRoot, tip_block >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, 
                                     tip_block >>
          /\ proposed_block' = defaultInitValue
          /\ pc' = [pc EXCEPT !["Node"] = "Done"]
          /\ UNCHANGED << txPool, tx_, actions >>

Node == Verify

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Producer \/ User \/ Node
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)
        /\ WF_vars(User)
        /\ WF_vars(Node)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
