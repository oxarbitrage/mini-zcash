-------------------------------- MODULE Utils -------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

\* from the community modules

(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class Functions.java   *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

FlattenSeq(seqs) ==
  (**************************************************************************)
  (* A sequence of all elements from all sequences in the sequence  seqs  . *)
  (*                                                                        *)
  (* Examples:                                                              *)
  (*                                                                        *)
  (*  FlattenSeq(<< <<1,2>>, <<1>> >>) = << 1, 2, 1 >>                      *)
  (*  FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>                     *)
  (*  FlattenSeq(<< "a", "b" >>) = "ab"                                     *)
  (**************************************************************************)
  IF Len(seqs) = 0 THEN seqs ELSE
    \* Not via  FoldSeq(\o, <<>>, seqs)  here to support strings with TLC.
    LET flatten[i \in 1..Len(seqs)] ==
        IF i = 1 THEN seqs[i] ELSE flatten[i-1] \o seqs[i]
    IN flatten[Len(seqs)]

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

Remove(s, e) ==
    (************************************************************************)
    (* The sequence s with e removed or s iff e \notin Range(s)             *)
    (************************************************************************)
    SelectSeq(s, LAMBDA t: t # e)

=============================================================================
