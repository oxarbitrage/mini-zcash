---- MODULE definitions ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE utils
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

\* Verify a given block header.
VerifyBlockHeader(proposed_block, tip_block) == TRUE

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

\* Given some text and a tree, create a new tree hash.
UpdateTree(tree, text) == RandomHash(4)

GenerateZKProof(data, previousProof) ==
    \* Generate a zk-SNARK proof summarizing the current state
    RandomHash(6)

VerifyZKProof(proof, noteCommitmentProof, nullifierProof) == TRUE

\* Create a transaction for a given set of actions.
OrchardTransaction(actions, proof) == [
    actions |-> actions,
    proof |-> GenerateZKProof(actions, proof)
]

====
