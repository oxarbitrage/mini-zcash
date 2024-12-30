---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Utils, Definitions

\* Define the set of users
CONSTANT Users

\* Define the process ids
MinerProccessId == 10000
NodeProccessId == 10001
UserProccessId == 1

(*--algorithm protocol

variables
    \* The root of the note commitment tree
    noteCommitmentTreeRoot = "";
    \* The root of the nullifier tree
    nullifierTreeRoot = "";
    \* The blockchain accepted tip block
    tip_block = [height |-> 1, transactions |-> <<>>];
    \* Transaction pool for miners
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

\* Mine transactions and add them to the blockchain.
fair process Miner = MinerProccessId
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
            nullifier |-> RandomHash(6),
            commitment |-> RandomHash(6),
            value |-> 10,
            receiver |-> "receiver"
        ]};

        tx_ := OrchardTransaction(actions);
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
                if VerifyTransaction(tx, nullifierTreeRoot, noteCommitmentTreeRoot) then
                    with action \in tx.actions do
                        nullifierTreeRoot := UpdateTree(nullifierTreeRoot, action.nullifier);
                        noteCommitmentTreeRoot := UpdateTree(noteCommitmentTreeRoot, action.commitment);
                    end with;
                end if;
            end with;
        end if;
        \* Valid or not, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bb706f6" /\ chksum(tla) = "c2b7ca71")
CONSTANT defaultInitValue
VARIABLES noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
          proposed_block, pc

(* define statement *)
HeightAlwaysIncreases == [][tip_block'.height > tip_block.height]_tip_block


TransactionsEventuallyProcessed ==
    (Cardinality(txPool) > 0) => <> (Cardinality(txPool) = 0)


NoDoubleSpending ==
    \A tx \in txPool :
        \A action1, action2 \in tx.actions :
            action1 /= action2 => action1.nullifier /= action2.nullifier

VARIABLES tx_, actions

vars == << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
           proposed_block, pc, tx_, actions >>

ProcSet == {MinerProccessId} \cup (UserProccessId .. Cardinality(Users)) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentTreeRoot = ""
        /\ nullifierTreeRoot = ""
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ actions = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = MinerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Cardinality(Users) -> "CreateTx"
                                        [] self = NodeProccessId -> "Verify"]

Mine == /\ pc[MinerProccessId] = "Mine"
        /\ Cardinality(txPool) > 0
        /\ proposed_block' = [height |-> tip_block.height + 1, txs |-> txPool]
        /\ txPool' = {}
        /\ pc' = [pc EXCEPT ![MinerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, 
                        tx_, actions >>

Miner == Mine

CreateTx(self) == /\ pc[self] = "CreateTx"
                  /\ txPool = {}
                  /\ actions' = [actions EXCEPT ![self] =            {[
                                                              nullifier |-> RandomHash(6),
                                                              commitment |-> RandomHash(6),
                                                              value |-> 10,
                                                              receiver |-> "receiver"
                                                          ]}]
                  /\ tx_' = [tx_ EXCEPT ![self] = OrchardTransaction(actions'[self])]
                  /\ txPool' = {tx_'[self]}
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot, 
                                  tip_block, proposed_block >>

User(self) == CreateTx(self)

Verify == /\ pc[NodeProccessId] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ \E tx \in proposed_block.txs:
                          IF VerifyTransaction(tx, nullifierTreeRoot, noteCommitmentTreeRoot)
                             THEN /\ \E action \in tx.actions:
                                       /\ nullifierTreeRoot' = UpdateTree(nullifierTreeRoot, action.nullifier)
                                       /\ noteCommitmentTreeRoot' = UpdateTree(noteCommitmentTreeRoot, action.commitment)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << noteCommitmentTreeRoot, 
                                                  nullifierTreeRoot >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot >>
          /\ proposed_block' = defaultInitValue
          /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
          /\ UNCHANGED << tip_block, txPool, tx_, actions >>

Node == Verify

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Miner \/ Node
           \/ (\E self \in UserProccessId .. Cardinality(Users): User(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Miner)
        /\ \A self \in UserProccessId .. Cardinality(Users) : WF_vars(User(self))
        /\ WF_vars(Node)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
