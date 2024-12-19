---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Utils

\* Define the set of users
CONSTANT Users

\* Define the process ids
MinerProccessId == 10000
NodeProccessId == 20000
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
    txPool = <<>>;
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
        await Len(txPool) > 0;
        \* Add tranactions to a block and propose it to the blockchain
        proposed_block := [height |-> tip_block.height + 1, transactions |-> txPool];
        \* Clear the transaction pool
        txPool := <<>>;
end process;

\* For each user, create transactions and add them to the transaction pool.
process User \in UserProccessId .. Len(SetToSeq(Users))
variables tx, username = SetToSeq(Users)[self - UserProccessId + 1];
begin
    CreateTransactions:
        tx := Def!CreateTransaction(
            username,
            <<Def!GenerateNewNote(username, 1, "null" \o username)>>,
            {"null" \o username}
        );
        txPool := Append(txPool, tx);
end process;

\* Verify proposed block and it's transactions. Update the note commitment and nullifier trees.
process Node = NodeProccessId
begin
    Verifier:
        \* Wait for a block proposal
        await proposed_block # defaultInitValue;
    
        if Def!VerifyBlockHeader(proposed_block, tip_block) then        
            with block_tx \in ToSet(proposed_block.transactions) do
                if Def!VerifyTransaction(block_tx, nullifierTreeRoot, noteCommitmentTreeRoot) then
                    \* Update the note commitment tree with new notes from the transaction.
                    noteCommitmentTreeRoot := Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes);
                    \* Update the nullifier tree with nullifiers from the transaction.
                    nullifierTreeRoot := Def!UpdateTree(nullifierTreeRoot, block_tx.nullifiers)
                end if;
            end with;
        end if;
        \* Valid or not, discard the proposed block after verification.
        proposed_block := defaultInitValue;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "431ac539" /\ chksum(tla) = "abbf929d")
CONSTANT defaultInitValue
VARIABLES noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
          proposed_block, pc

(* define statement *)
LOCAL Def == INSTANCE Definitions

VARIABLES tx, username

vars == << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, txPool, 
           proposed_block, pc, tx, username >>

ProcSet == {MinerProccessId} \cup (UserProccessId .. Len(SetToSeq(Users))) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentTreeRoot = ""
        /\ nullifierTreeRoot = ""
        /\ tip_block = [height |-> 1, transactions |-> <<>>]
        /\ txPool = <<>>
        /\ proposed_block = defaultInitValue
        (* Process User *)
        /\ tx = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> defaultInitValue]
        /\ username = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> SetToSeq(Users)[self - UserProccessId + 1]]
        /\ pc = [self \in ProcSet |-> CASE self = MinerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Len(SetToSeq(Users)) -> "CreateTransactions"
                                        [] self = NodeProccessId -> "Verifier"]

Mine == /\ pc[MinerProccessId] = "Mine"
        /\ Len(txPool) > 0
        /\ proposed_block' = [height |-> tip_block.height + 1, transactions |-> txPool]
        /\ txPool' = <<>>
        /\ pc' = [pc EXCEPT ![MinerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot, tip_block, 
                        tx, username >>

Miner == Mine

CreateTransactions(self) == /\ pc[self] = "CreateTransactions"
                            /\ tx' = [tx EXCEPT ![self] =       Def!CreateTransaction(
                                                              username[self],
                                                              <<Def!GenerateNewNote(username[self], 1, "null" \o username[self])>>,
                                                              {"null" \o username[self]}
                                                          )]
                            /\ txPool' = Append(txPool, tx'[self])
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << noteCommitmentTreeRoot, 
                                            nullifierTreeRoot, tip_block, 
                                            proposed_block, username >>

User(self) == CreateTransactions(self)

Verifier == /\ pc[NodeProccessId] = "Verifier"
            /\ proposed_block # defaultInitValue
            /\ IF Def!VerifyBlockHeader(proposed_block, tip_block)
                  THEN /\ \E block_tx \in ToSet(proposed_block.transactions):
                            IF Def!VerifyTransaction(block_tx, nullifierTreeRoot, noteCommitmentTreeRoot)
                               THEN /\ noteCommitmentTreeRoot' = Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes)
                                    /\ nullifierTreeRoot' = Def!UpdateTree(nullifierTreeRoot, block_tx.nullifiers)
                               ELSE /\ TRUE
                                    /\ UNCHANGED << noteCommitmentTreeRoot, 
                                                    nullifierTreeRoot >>
                  ELSE /\ TRUE
                       /\ UNCHANGED << noteCommitmentTreeRoot, 
                                       nullifierTreeRoot >>
            /\ proposed_block' = defaultInitValue
            /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
            /\ UNCHANGED << tip_block, txPool, tx, username >>

Node == Verifier

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Miner \/ Node
           \/ (\E self \in UserProccessId .. Len(SetToSeq(Users)): User(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
