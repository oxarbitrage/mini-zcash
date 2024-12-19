---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Utils

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
    LOCAL Def == INSTANCE Definitions
end define;

\* Mine transactions and add them to the blockchain.
process Miner = MinerProccessId
begin
    Mine:
        \* As soon as we have transactions
        await Cardinality(txPool) > 0;
        \* Add tranactions to a block and propose it to the blockchain
        proposed_block := [height |-> tip_block.height + 1, txs |-> txPool];
        \* Clear the transaction pool
        txPool := {};
end process;

\* For each user, create transactions and add them to the transaction pool.
process User \in UserProccessId .. Cardinality(Users)
variables 
    tx_,
    username = SetToSeq(Users)[self],
    nullifier = "null" \o username;
begin
    CreateTransactions:
        tx_ := Def!CreateTransaction(
            username,
            {Def!GenerateNewNote(10, nullifier)},
            {nullifier}
        );
        txPool := txPool \cup {tx_};
end process;

\* Verify proposed block and it's transactions. Update the note commitment and nullifier trees.
process Node = NodeProccessId
begin
    Verify:
        \* Wait for a block proposal
        await proposed_block # defaultInitValue;
    
        if Def!VerifyBlockHeader(proposed_block, tip_block) then        
            with tx \in proposed_block.txs do
                if Def!VerifyTransaction(tx, nullifierTreeRoot, noteCommitmentTreeRoot) then
                    \* Update the note commitment tree with new notes from the transaction.
                    noteCommitmentTreeRoot := Def!UpdateTree(noteCommitmentTreeRoot, tx.newNotes);
                    \* Update the nullifier tree with nullifiers from the transaction.
                    nullifierTreeRoot := Def!UpdateTree(nullifierTreeRoot, tx.nullifiers)
                end if;
            end with;
        end if;
        \* Valid or not, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7e550db3" /\ chksum(tla) = "77cc42b")
CONSTANT defaultInitValue
VARIABLES noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
          proposed_block, pc

(* define statement *)
LOCAL Def == INSTANCE Definitions

VARIABLES tx_, username, nullifier

vars == << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
           proposed_block, pc, tx_, username, nullifier >>

ProcSet == {MinerProccessId} \cup (UserProccessId .. Cardinality(Users)) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentTreeRoot = ""
        /\ nullifierTreeRoot = ""
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = {}
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx_ = [self \in UserProccessId .. Cardinality(Users) |-> defaultInitValue]
        /\ username = [self \in UserProccessId .. Cardinality(Users) |-> SetToSeq(Users)[self]]
        /\ nullifier = [self \in UserProccessId .. Cardinality(Users) |-> "null" \o username[self]]
        /\ pc = [self \in ProcSet |-> CASE self = MinerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Cardinality(Users) -> "CreateTransactions"
                                        [] self = NodeProccessId -> "Verify"]

Mine == /\ pc[MinerProccessId] = "Mine"
        /\ Cardinality(txPool) > 0
        /\ proposed_block' = [height |-> tip_block.height + 1, txs |-> txPool]
        /\ txPool' = {}
        /\ pc' = [pc EXCEPT ![MinerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, 
                        tx_, username, nullifier >>

Miner == Mine

CreateTransactions(self) == /\ pc[self] = "CreateTransactions"
                            /\ tx_' = [tx_ EXCEPT ![self] =        Def!CreateTransaction(
                                                                username[self],
                                                                {Def!GenerateNewNote(10, nullifier[self])},
                                                                {nullifier[self]}
                                                            )]
                            /\ txPool' = (txPool \cup {tx_'[self]})
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << noteCommitmentTreeRoot, 
                                            nullifierTreeRoot, tip_block, 
                                            proposed_block, username, 
                                            nullifier >>

User(self) == CreateTransactions(self)

Verify == /\ pc[NodeProccessId] = "Verify"
          /\ proposed_block # defaultInitValue
          /\ IF Def!VerifyBlockHeader(proposed_block, tip_block)
                THEN /\ \E tx \in proposed_block.txs:
                          IF Def!VerifyTransaction(tx, nullifierTreeRoot, noteCommitmentTreeRoot)
                             THEN /\ noteCommitmentTreeRoot' = Def!UpdateTree(noteCommitmentTreeRoot, tx.newNotes)
                                  /\ nullifierTreeRoot' = Def!UpdateTree(nullifierTreeRoot, tx.nullifiers)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << noteCommitmentTreeRoot, 
                                                  nullifierTreeRoot >>
                ELSE /\ TRUE
                     /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot >>
          /\ proposed_block' = defaultInitValue
          /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
          /\ UNCHANGED << tip_block, txPool, tx_, username, nullifier >>

Node == Verify

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Miner \/ Node
           \/ (\E self \in UserProccessId .. Cardinality(Users): User(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
