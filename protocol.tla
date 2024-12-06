---- MODULE protocol ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Utils

\* Define the set of users
CONSTANT Users

\* Define the process ids
MinerProccessId == 10000
NodeProccessId == 20000
ScannerProccessId == 1000
UserProccessId == 1

(*--algorithm protocol

variables
    \* Initial root of an empty tree
    noteCommitmentTreeRoot = <<>>;
    \* Set of spent note nullifiers
    nullifierSet = {};
    \* Sequence of incoming blocks
    blocks = <<>>;
    \* User public/private keys
    userKeys = [u \in Users |-> Def!GenerateKeyPair(u)];
    \* Each user's locally tracked notes, initial balance for each user is 10.
    userNotes = [u \in Users |-> <<[receiver |-> "pk" \o u, value |-> 1, nullifier |-> "init" \o u]>>];
    \* Transaction pool for miners
    txPool = <<>>;

define
    LOCAL Def == INSTANCE Definitions
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

\* For each user, create unspent transactions and add them to the transaction pool.
process User \in UserProccessId .. Len(SetToSeq(Users))
variables tx, username;
begin
    CreateTransactions:
        username := SetToSeq(Users)[self];
        tx := Def!CreateTransaction(username, Def!GenerateNewNotes(username, 1, "null" \o ToString(self)), {});
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
        
        \* Verify transactions and update the note commitment tree
        with block_tx \in ToSet(block.transactions) do
            if Def!VerifyTransaction(block_tx, nullifierSet) then
                noteCommitmentTreeRoot := Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes);
                nullifierSet := nullifierSet \cup block_tx.nullifiers;

                \* Decrypt notes and add them to the user's notes                
                with note \in ToSet(block_tx.newNotes) do
                    with user \in DOMAIN userKeys do
                        if Def!CanDecrypt(note, userKeys[user]) then
                            userNotes[user] := Append(userNotes[user], note);
                        end if;
                    end with;
                end with;
            end if;
        end with;
end process;

\* Scan the user note commitment tree and calculate the user's balance.
process Scanner \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users))
variables userBalance = 0, userName = SetToSeq(Users)[self - ScannerProccessId], c = 1;
begin
    Scan:
        \* Calculate the user's balance
        userBalance := Def!SumValidValues(userNotes[userName], nullifierSet);
        \* Check if the user's balance is greater than 1 if the user has more than one note.
        if Len(userNotes[userName]) > 1 then
            assert userBalance > 1;
        end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "46ac69d3" /\ chksum(tla) = "ea6b05bf")
CONSTANT defaultInitValue
VARIABLES noteCommitmentTreeRoot, nullifierSet, blocks, userKeys, userNotes, 
          txPool, pc

(* define statement *)
LOCAL Def == INSTANCE Definitions

VARIABLES tx, username, block, userBalance, userName, c

vars == << noteCommitmentTreeRoot, nullifierSet, blocks, userKeys, userNotes, 
           txPool, pc, tx, username, block, userBalance, userName, c >>

ProcSet == {MinerProccessId} \cup (UserProccessId .. Len(SetToSeq(Users))) \cup {NodeProccessId} \cup (ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)))

Init == (* Global variables *)
        /\ noteCommitmentTreeRoot = <<>>
        /\ nullifierSet = {}
        /\ blocks = <<>>
        /\ userKeys = [u \in Users |-> Def!GenerateKeyPair(u)]
        /\ userNotes = [u \in Users |-> <<[receiver |-> "pk" \o u, value |-> 1, nullifier |-> "init" \o u]>>]
        /\ txPool = <<>>
        (* Process User *)
        /\ tx = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> defaultInitValue]
        /\ username = [self \in UserProccessId .. Len(SetToSeq(Users)) |-> defaultInitValue]
        (* Process Node *)
        /\ block = defaultInitValue
        (* Process Scanner *)
        /\ userBalance = [self \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)) |-> 0]
        /\ userName = [self \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)) |-> SetToSeq(Users)[self - ScannerProccessId]]
        /\ c = [self \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)) |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self = MinerProccessId -> "Mine"
                                        [] self \in UserProccessId .. Len(SetToSeq(Users)) -> "CreateTransactions"
                                        [] self = NodeProccessId -> "Verifier"
                                        [] self \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)) -> "Scan"]

Mine == /\ pc[MinerProccessId] = "Mine"
        /\ Len(txPool) > 0
        /\ blocks' = Append(blocks, [transactions |-> txPool])
        /\ txPool' = <<>>
        /\ pc' = [pc EXCEPT ![MinerProccessId] = "Done"]
        /\ UNCHANGED << noteCommitmentTreeRoot, nullifierSet, userKeys, 
                        userNotes, tx, username, block, userBalance, userName, 
                        c >>

Miner == Mine

CreateTransactions(self) == /\ pc[self] = "CreateTransactions"
                            /\ username' = [username EXCEPT ![self] = SetToSeq(Users)[self]]
                            /\ tx' = [tx EXCEPT ![self] = Def!CreateTransaction(username'[self], Def!GenerateNewNotes(username'[self], 1, "null" \o ToString(self)), {})]
                            /\ txPool' = Append(txPool, tx'[self])
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << noteCommitmentTreeRoot, 
                                            nullifierSet, blocks, userKeys, 
                                            userNotes, block, userBalance, 
                                            userName, c >>

User(self) == CreateTransactions(self)

Verifier == /\ pc[NodeProccessId] = "Verifier"
            /\ Len(blocks) > 0
            /\ block' = Head(blocks)
            /\ blocks' = Tail(blocks)
            /\ \E block_tx \in ToSet(block'.transactions):
                 IF Def!VerifyTransaction(block_tx, nullifierSet)
                    THEN /\ noteCommitmentTreeRoot' = Def!UpdateTree(noteCommitmentTreeRoot, block_tx.newNotes)
                         /\ nullifierSet' = (nullifierSet \cup block_tx.nullifiers)
                         /\ \E note \in ToSet(block_tx.newNotes):
                              \E user \in DOMAIN userKeys:
                                IF Def!CanDecrypt(note, userKeys[user])
                                   THEN /\ userNotes' = [userNotes EXCEPT ![user] = Append(userNotes[user], note)]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED userNotes
                    ELSE /\ TRUE
                         /\ UNCHANGED << noteCommitmentTreeRoot, nullifierSet, 
                                         userNotes >>
            /\ pc' = [pc EXCEPT ![NodeProccessId] = "Done"]
            /\ UNCHANGED << userKeys, txPool, tx, username, userBalance, 
                            userName, c >>

Node == Verifier

Scan(self) == /\ pc[self] = "Scan"
              /\ userBalance' = [userBalance EXCEPT ![self] = Def!SumValidValues(userNotes[userName[self]], nullifierSet)]
              /\ IF Len(userNotes[userName[self]]) > 1
                    THEN /\ Assert(userBalance'[self] > 1, 
                                   "Failure of assertion at line 94, column 13.")
                    ELSE /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << noteCommitmentTreeRoot, nullifierSet, blocks, 
                              userKeys, userNotes, txPool, tx, username, block, 
                              userName, c >>

Scanner(self) == Scan(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Miner \/ Node
           \/ (\E self \in UserProccessId .. Len(SetToSeq(Users)): User(self))
           \/ (\E self \in ScannerProccessId + 1 .. ScannerProccessId + Len(SetToSeq(Users)): Scanner(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
