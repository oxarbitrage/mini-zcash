---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, definitions

\* Define the set of users
CONSTANT Users

\* Define the process ids
ProducerProccessId == 10000
NodeProccessId == 10001
UserProccessId == 1

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

\* Get transactions from the pool and add them as blocks to the blockchain.
fair process Producer = ProducerProccessId
begin
    Produce:
        \* As soon as we have transactions
        await Cardinality(txPool) > 0;
        \* Add transactions to a block and propose it to the blockchain
        proposed_block :=
        [
            height                  |-> tip_block.height + 1,
            txs                     |-> txPool,
            newNoteCommitmentRoot   |-> GenerateZKProof(txPool, noteCommitmentRoot),
            newNullifierRoot        |-> GenerateZKProof(txPool, nullifierRoot)
        ];
        \* Clear the transaction pool
        txPool := {};
end process;

\* For each user, create transactions and add them to the transaction pool.
fair process User \in UserProccessId .. Cardinality(Users)
variables 
    tx_,
    actions;
begin
    CreateTx:
        await txPool = {};
        actions :=
        {[
            nullifier   |-> RandomBytes(32),
            commitment  |-> RandomBytes(32),
            value       |-> 10,
            receiver    |-> "receiver"
        ]};
        tx_ := OrchardTransaction(actions, GenerateZKProof(actions, noteCommitmentRoot));
        txPool := {tx_};
end process;

\* Verify proposed block and update the state Merkle roots.
fair process Node = NodeProccessId
begin
    Verify:
        \* Wait for a block proposal.
        await proposed_block # defaultInitValue;
    
        if VerifyBlockHeader(proposed_block, tip_block) then
            \* Check that the block’s updated state proofs are consistent with the current state and its transactions.
            if ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs) = proposed_block.newNoteCommitmentRoot
                /\ ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs) = proposed_block.newNullifierRoot then
                  \* Update the compact state (Merkle roots) accordingly.
                  noteCommitmentRoot := proposed_block.newNoteCommitmentRoot;
                  nullifierRoot := proposed_block.newNullifierRoot;
            end if;
        end if;
        \* Regardless of validity, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d5771f43" /\ chksum(tla) = "e069472a")
CONSTANT defaultInitValue
VARIABLES pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
          proposed_block, tx_, actions

vars == << pc, noteCommitmentRoot, nullifierRoot, tip_block, txPool, 
           proposed_block, tx_, actions >>

ProcSet == {ProducerProccessId} \cup (UserProccessId .. Cardinality(Users)) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentRoot = <<>>
        /\ nullifierRoot = <<>>
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ actions = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = ProducerProccessId -> "Produce"
                                        [] self \in UserProccessId .. Cardinality(Users) -> "CreateTx"
                                        [] self = NodeProccessId -> "Verify"]

Produce == /\ pc[ProducerProccessId] = "Produce"
           /\ Cardinality(txPool) > 0
           /\ proposed_block' = [
                                    height                  |-> tip_block.height + 1,
                                    txs                     |-> txPool,
                                    newNoteCommitmentRoot   |-> GenerateZKProof(txPool, noteCommitmentRoot),
                                    newNullifierRoot        |-> GenerateZKProof(txPool, nullifierRoot)
                                ]
           /\ txPool' = {}
           /\ pc' = [pc EXCEPT ![ProducerProccessId] = "Done"]
           /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, tx_, 
                           actions >>

Producer == Produce

CreateTx(self) == /\ pc[self] = "CreateTx"
                  /\ txPool = {}
                  /\ actions' = [actions EXCEPT ![self] = {[
                                                              nullifier   |-> RandomBytes(32),
                                                              commitment  |-> RandomBytes(32),
                                                              value       |-> 10,
                                                              receiver    |-> "receiver"
                                                          ]}]
                  /\ tx_' = [tx_ EXCEPT ![self] = OrchardTransaction(actions'[self], GenerateZKProof(actions'[self], noteCommitmentRoot))]
                  /\ txPool' = {tx_'[self]}
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << noteCommitmentRoot, nullifierRoot, tip_block, 
                                  proposed_block >>

User(self) == CreateTx(self)

Verify == /\ pc[NodeProccessId] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ IF ComputeNewNoteRoot(noteCommitmentRoot, proposed_block.txs) = proposed_block.newNoteCommitmentRoot
                            /\ ComputeNewNullifierRoot(nullifierRoot, proposed_block.txs) = proposed_block.newNullifierRoot
                           THEN /\ noteCommitmentRoot' = proposed_block.newNoteCommitmentRoot
                                /\ nullifierRoot' = proposed_block.newNullifierRoot
                           ELSE /\ TRUE
                                /\ UNCHANGED << noteCommitmentRoot, 
                                                nullifierRoot >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentRoot, nullifierRoot >>
          /\ proposed_block' = defaultInitValue
          /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
          /\ UNCHANGED << tip_block, txPool, tx_, actions >>

Node == Verify

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Producer \/ Node
           \/ (\E self \in UserProccessId .. Cardinality(Users): User(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)
        /\ \A self \in UserProccessId .. Cardinality(Users) : WF_vars(User(self))
        /\ WF_vars(Node)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
