---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, utils, definitions

\* Define the set of users
CONSTANT Users

\* Define the process ids
ProducerProccessId == 10000
NodeProccessId == 10001
UserProccessId == 1

(*--algorithm protocol

variables
    \* A compact zk-SNARK proof that summarizes the mnerkle tree of all note commitments.
    noteCommitmentProof = "";
    \* A compact zk-SNARK proof that summarizes the mnerkle tree of all nullifiers.
    nullifierProof = "";
    \* The blockchain accepted tip block
    tip_block = [height |-> 1, transactions |-> <<>>];
    \* Transaction pool for producers to build blocks
    txPool = {};
    \* The proposed block from a mniner
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

\* Get transactions from the pool and add them as blocks to the blockchain.
fair process Producer = ProducerProccessId
begin
    Mine:
        \* As soon as we have transactions
        await Cardinality(txPool) > 0;
        \* Add transactions to a block and propose it to the blockchain
        proposed_block := [height |-> tip_block.height + 1, txs |-> txPool];
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
        actions := {[
            nullifier |-> RandomHash(4),
            commitment |-> RandomHash(4),
            value |-> 10,
            receiver |-> "receiver"
        ]};
        \* need nullifir?
        tx_ := OrchardTransaction(actions, GenerateZKProof(actions, noteCommitmentProof));
        txPool := {tx_};
end process;

\* Verify proposed block and it's transactions. Update the note commitment and nullifier trees.
fair process Node = NodeProccessId
begin
    Verify:
        \* Wait for a block proposal
        await proposed_block # defaultInitValue;
    
        if VerifyBlockHeader(proposed_block, tip_block) then
            with tx \in proposed_block.txs do
                if VerifyZKProof(tx.proof, noteCommitmentProof, nullifierProof) then
                    with action \in tx.actions do
                        \* Update the note commitment and nullifier trees, generate new compact proofs for them.
                        noteCommitmentProof := GenerateZKProof(action.nullifier, noteCommitmentProof);
                        nullifierProof := GenerateZKProof(action.commitment, nullifierProof);
                    end with;
                end if;
            end with;
        end if;
        \* Valid or not, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2685806f" /\ chksum(tla) = "a9f6492a")
CONSTANT defaultInitValue
VARIABLES pc, noteCommitmentProof, nullifierProof, tip_block, txPool, 
          proposed_block

(* define statement *)
HeightAlwaysIncreases == [][tip_block'.height > tip_block.height]_tip_block


TransactionsEventuallyProcessed ==
    (Cardinality(txPool) > 0) => <> (Cardinality(txPool) = 0)


NoDoubleSpending ==
    \A tx \in txPool :
        \A action1, action2 \in tx.actions :
            action1 /= action2 => action1.nullifier /= action2.nullifier

VARIABLES tx_, actions

vars == << pc, noteCommitmentProof, nullifierProof, tip_block, txPool, 
           proposed_block, tx_, actions >>

ProcSet == {ProducerProccessId} \cup (UserProccessId .. Cardinality(Users)) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentProof = ""
        /\ nullifierProof = ""
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ actions = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = ProducerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Cardinality(Users) -> "CreateTx"
                                        [] self = NodeProccessId -> "Verify"]

Mine == /\ pc[ProducerProccessId] = "Mine"
        /\ Cardinality(txPool) > 0
        /\ proposed_block' = [height |-> tip_block.height + 1, txs |-> txPool]
        /\ txPool' = {}
        /\ pc' = [pc EXCEPT ![ProducerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentProof, nullifierProof, tip_block, tx_, 
                        actions >>

Producer == Mine

CreateTx(self) == /\ pc[self] = "CreateTx"
                  /\ txPool = {}
                  /\ actions' = [actions EXCEPT ![self] =            {[
                                                              nullifier |-> RandomHash(4),
                                                              commitment |-> RandomHash(4),
                                                              value |-> 10,
                                                              receiver |-> "receiver"
                                                          ]}]
                  /\ tx_' = [tx_ EXCEPT ![self] = OrchardTransaction(actions'[self], GenerateZKProof(actions'[self], noteCommitmentProof))]
                  /\ txPool' = {tx_'[self]}
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << noteCommitmentProof, nullifierProof, 
                                  tip_block, proposed_block >>

User(self) == CreateTx(self)

Verify == /\ pc[NodeProccessId] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ \E tx \in proposed_block.txs:
                          IF VerifyZKProof(tx.proof, noteCommitmentProof, nullifierProof)
                             THEN /\ \E action \in tx.actions:
                                       /\ noteCommitmentProof' = GenerateZKProof(action.nullifier, noteCommitmentProof)
                                       /\ nullifierProof' = GenerateZKProof(action.commitment, nullifierProof)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << noteCommitmentProof, 
                                                  nullifierProof >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentProof, nullifierProof >>
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
