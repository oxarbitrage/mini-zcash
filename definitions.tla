---- MODULE Definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Utils
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
LOCAL INSTANCE Randomization

\* Define a set of characters
CHARACTERS == {
    "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v",
    "w", "x", "y", "z", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F", "G", "H", "I",
    "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "!", "@", "#", "$", "%", "^",
    "&", "*", "(", ")", "-", "_", "+", "=", "{", "}", "[", "]", "|", ":", ";", "<", ">", ",", ".", "?"
}

\* Generate a key pair for a given user.
GenerateKeyPair(user) == [publicKey |-> "pk_" \o user, privateKey |-> "sk_" \o user]

\* Verify a given proof.
VerifyProof(proof) == TRUE

\* Check if a transaction is valid.
IsValidTransaction(tx) ==
    /\ tx.sender /= ""
    /\ Len(tx.newNotes) > 0
    /\ Cardinality(tx.nullifiers) > 0

\* Check if a transaction is valid and its nullifiers are not in the given set.
VerifyTransaction(tx, nullifierSet) ==
    /\ IsValidTransaction(tx)
    /\ tx.nullifiers \cap nullifierSet = {}
    /\ VerifyProof(tx.proof)

\* Convert a sequence of characters to a string.
RECURSIVE SeqToString(_)
SeqToString(seq) ==
    IF seq = <<>> THEN ""
    ELSE Head(seq) \o SeqToString(Tail(seq))

\* Generate a random hash of a given length.
(* TODO: Maybe use:
https://github.com/tlaplus/Examples/blob/master/specifications/tower_of_hanoi/Bits.java
https://stackoverflow.com/questions/72350178/how-to-create-an-array-where-each-index-has-a-random-number
*)
RandomHash(n) == SeqToString(SetToSeq(RandomSubset(n, CHARACTERS)))

\* Append a new note to the note commitment tree.
UpdateTree(treeRoot, newNotes) == Append(treeRoot, RandomHash(6))

\* Check if a note can be decrypted by a given user.
CanDecrypt(note, userKey) ==
    /\ note.receiver = userKey.publicKey
    /\ note.value > 0

\* Generate a proof for a given user.
GenerateProof(user, newNotes, nullifiers) ==
    \* TODO: Implement some sort of proof generation
    RandomHash(6)

\* Create a transaction for a given user.
CreateTransaction(user, newNotes, nullifiers) ==
    IF Len(newNotes) > 0 THEN
        [sender |-> user,
         newNotes |-> newNotes,
         nullifiers |-> nullifiers,
         proof |-> GenerateProof(user, newNotes, nullifiers)]
    ELSE
        [error |-> "Invalid transaction"]

\* Generate new notes for a given user.
GenerateNewNotes(user, value, nullifier) ==
    <<
        [receiver |-> "pk_" \o user,
        value |-> value,
        nullifier |-> RandomHash(6)]
    >>

\* Sum the values of a sequence of transactions.
RECURSIVE SumValues(_)
SumValues(seq) == 
    IF seq = <<>> THEN 0
    ELSE Head(seq).value + SumValues(Tail(seq))

\* Sum the values of a sequence of transactions, excluding those with nullifiers in the given set.
RECURSIVE SumValidValues(_, _)
SumValidValues(seq, nullifierSet) ==
    SumValues(
        Remove(
            [i \in 1..Len(seq) |-> IF seq[i].nullifier \notin nullifierSet THEN seq[i] ELSE <<>>],
            <<>>
        )
    )

====