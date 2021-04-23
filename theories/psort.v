Require Import Arith Sorted Permutation List DivConq msort. 
Import List.ListNotations.
Open Scope list_scope.

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extraction Language OCaml.
Set Extraction AccessOpaque.

Definition sorted := Sorted le.
Definition permutation := @Permutation nat.

Lemma pair_merge_prog : forall (a1 a2 : nat) (l l' l'0 : list nat),
  sorted l' -> permutation l' l -> 
  sorted l'0 -> permutation l'0 [a1; a2] ->
  {l'1 : list nat | sorted l'1 /\ permutation l'1 (a1 :: a2 :: l)}.
Proof.
intros; exists (merge l'0 l'); split.
- apply merge_sorted; auto.
- rewrite permutation_merge_concat, H0, H2; simpl; repeat constructor; auto.
Defined.

Lemma psort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
apply div_conq_pair.
- exists []; split; constructor.
- intros; exists [a]; split; constructor; constructor.
- intros; destruct (le_lt_dec a1 a2).
  + exists [a1; a2]; split; repeat constructor; auto.
  + exists [a2; a1]; split; repeat constructor; apply Nat.lt_le_incl; auto.
- intros; destruct H,H0,a,a0; 
  eapply pair_merge_prog. apply H1. auto. apply H. auto.
Defined.

Extraction "extraction/psort.ml" psort_prog.
