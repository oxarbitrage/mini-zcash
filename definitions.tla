---- MODULE Definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Utils

\* Generate a key pair for a given user.
GenerateKeyPair(user) == [publicKey |-> "pk_" \o user, privateKey |-> "sk_" \o user]

\* Verify a given proof.
VerifyProof(proof) == TRUE

\* Verify a given transaction.
VerifyTransaction(tx, nullifierSet) == IF tx.nullifiers \cap nullifierSet /= {} THEN FALSE ELSE VerifyProof(tx.proof)

\* Placeholder for a hash function.
Hash(data) == data

\*
UpdateTree(treeRoot, newNotes) == Hash(Append(treeRoot, FlattenSeq(newNotes)))

\*
CanDecrypt(note, userKey) ==
    \*note.receiver = userKey.publicKey
    TRUE

\*
GenerateProof(user, newNotes, nullifiers) ==
    \* Hash(user \o FlattenSeq(newNotes) \o nullifiers)
    Hash(user)

\*
CreateTransaction(user, newNotes, nullifiers) == [sender |-> user,
    newNotes |-> newNotes,
    nullifiers |-> nullifiers,
    proof |-> GenerateProof(user, newNotes, nullifiers)]

\*
GenerateNewNotes(user, value, nullifier) ==
    <<[receiver |-> "pk" \o user, value |-> value, nullifier |-> nullifier]>>

\* Sum the values of a sequence of transactions.
RECURSIVE SumValues(_)
SumValues(seq) == 
    IF seq = <<>> THEN 0
    ELSE Head(seq).value + SumValues(Tail(seq))

\* Sum the values of a sequence of transactions, excluding those with nullifiers in the given set.
SumValidValues(seq, nullifierSet) ==
    SumValues([i \in 1..Len(seq) |-> IF seq[i].nullifier \notin nullifierSet THEN seq[i] ELSE <<>>])

====