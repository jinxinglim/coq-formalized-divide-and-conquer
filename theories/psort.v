Require Import Arith Sorted Permutation List DivConq msort. 
Import List.ListNotations.
Open Scope list_scope.

From Hammer Require Import Hammer.

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
- apply merge_sorted; ssimpl.
- rewrite permutation_merge_concat, H0, H2; sauto.
Defined.

Lemma psort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
apply div_conq_pair.
- sauto.
- sauto.
- intros; destruct (le_lt_dec a1 a2).
  + sauto.
  + exists [a2; a1]; sauto.
- ssimpl; eapply pair_merge_prog. apply H1. sauto. apply H0. sauto.
Defined.

Extraction "extraction/psort.ml" psort_prog.
