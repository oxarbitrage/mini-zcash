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
    noteCommitmentTreeRoot = "init";
    \* The root of the nullifier tree
    nullifierTreeRoot = "init";
    \* Sequence of incoming blocks
    blocks = <<>>;
    \* Transaction pool for miners
    txPool = <<>>;

define
    LOCAL Def == INSTANCE Definitions

    NoDoubleSpending ==
        \A block \in ToSet(blocks) :
            \A tx1, tx2 \in block.transactions :
                tx1 /= tx2 => tx1.nullifiers \cap tx2.nullifiers = {}
end define;

\* Mine transactions and add them to the blockchain.
process Miner = MinerProccessId
begin
    Mine:
        \* As soon as we have transactions
        await Len(txPool) > 0;
        \* Add tranactions to a block and a new block to the blockchain
        blocks := Append(blocks, [transactions |-> txPool]);
        \* Clear the transaction pool
        txPool := <<>>;    
end process;

\* For each user, create transactions that spend notes and add them to the transaction pool.
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

\* Verify transactions and update the note commitment tree.
process Node = NodeProccessId
variables block;
begin
    Verifier:
        \* Wait for blocks
        await Len(blocks) > 0;
        \* Get the first block
        block := Head(blocks);
        \* Remove processed block
        blocks := Tail(blocks);
        
        \* Verify transactions, update the note commitment tree and the nullifier set
        with block_tx \in ToSet(block.transactions) do
            if Def!VerifyTransaction(block_tx, nullifierTreeRoot, noteCommitmentTreeRoot) then
                noteCommitmentTreeRoot := Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes);
                nullifierTreeRoot := Def!UpdateTree(nullifierTreeRoot, block_tx.nullifiers)
            end if;
        end with;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ae4e1770" /\ chksum(tla) = "6dfd9c69")
CONSTANT defaultInitValue
VARIABLES noteCommitmentTreeRoot, nullifierTreeRoot, blocks, txPool, pc

(* define statement *)
LOCAL Def == INSTANCE Definitions

NoDoubleSpending ==
    \A block \in ToSet(blocks) :
        \A tx1, tx2 \in block.transactions :
            tx1 /= tx2 => tx1.nullifiers \cap tx2.nullifiers = {}

VARIABLES tx, username, block

vars == << noteCommitmentTreeRoot, nullifierTreeRoot, blocks, txPool, pc, tx, 
           username, block >>

ProcSet == {MinerProccessId} \cup (UserProccessId .. Len(SetToSeq(Users))) \cup {NodeProccessId}

Init == (* Global variables *)
        /\ noteCommitmentTreeRoot = "init"
        /\ nullifierTreeRoot = "init"
        /\ blocks = <<>>
        /\ txPool = <<>>
        (* Process User *)
        /\ tx = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> defaultInitValue]
        /\ username = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> SetToSeq(Users)[self - UserProccessId + 1]]
        (* Process Node *)
        /\ block = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = MinerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Len(SetToSeq(Users)) -> "CreateTransactions"
                                        [] self = NodeProccessId -> "Verifier"]

Mine == /\ pc[MinerProccessId] = "Mine"
        /\ Len(txPool) > 0
        /\ blocks' = Append(blocks, [transactions |-> txPool])
        /\ txPool' = <<>>
        /\ pc' = [pc EXCEPT ![MinerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentTreeRoot, nullifierTreeRoot, tx, 
                        username, block >>

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
                                            nullifierTreeRoot, blocks, 
                                            username, block >>

User(self) == CreateTransactions(self)

Verifier == /\ pc[NodeProccessId] = "Verifier"
            /\ Len(blocks) > 0
            /\ block' = Head(blocks)
            /\ blocks' = Tail(blocks)
            /\ \E block_tx \in ToSet(block'.transactions):
                 IF Def!VerifyTransaction(block_tx, nullifierTreeRoot, noteCommitmentTreeRoot)
                    THEN /\ noteCommitmentTreeRoot' = Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes)
                         /\ nullifierTreeRoot' = Def!UpdateTree(nullifierTreeRoot, block_tx.nullifiers)
                    ELSE /\ TRUE
                         /\ UNCHANGED << noteCommitmentTreeRoot, 
                                         nullifierTreeRoot >>
            /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
            /\ UNCHANGED << txPool, tx, username >>

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
