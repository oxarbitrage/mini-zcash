---- MODULE definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC

\* Verify a given block header.
VerifyBlockHeader(proposed_block, tip_block) == TRUE

\* Generate a sequence of random bytes of length n.
RandomBytes(n) == [ i \in 1..n |-> CHOOSE x \in 0..255 : TRUE ]

\* Generate a zk-SNARK proof summarizing the current state
GenerateZKProof(data, previousProof) == RandomBytes(4992)

\* Abstract function that computes a new note commitment root given the current state and a set of transactions.
ComputeNewNoteRoot(oldProof, txs) == RandomBytes(32)

\* Abstract function that computes a new nullifier root given the current state and a set of transactions.
ComputeNewNullifierRoot(oldProof, txs) == RandomBytes(32)

\* Verify a zk-SNARK proof.
VerifyZKProof(proof, noteCommitmentProof, nullifierProof) == TRUE

\* Create a transaction for a given set of actions.
OrchardTransaction(actions, proof) == [
    actions |-> actions,
    proof |-> GenerateZKProof(actions, proof)
]

====
