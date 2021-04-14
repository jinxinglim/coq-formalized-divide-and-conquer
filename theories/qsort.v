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

Section PermSplitPivot.

Variable A : Type.
Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.
Implicit Type l : list A.

Lemma Permutation_split_pivot: forall (a : A) l,
  Permutation (fst (split_pivot A le le_dec a l) 
    ++ snd (split_pivot A le le_dec a l)) l.
Proof.
induction l; ssimpl; rewrite <- Permutation_middle; constructor; sauto.
Defined.

End PermSplitPivot.

Lemma qsort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
unshelve eapply div_conq_pivot. exact le. exact le_dec.
- sauto.
- ssimpl; exists (merge l'0 (a :: l')); split.
  + apply merge_sorted; ssimpl. constructor; ssimpl.
    assert (Forall (le a) l').
    eapply Permutation_Forall. apply Permutation_sym; apply H2.
    apply Forall_snd_split_pivot; ssimpl.
    sauto.
 + rewrite permutation_merge_concat, <- Permutation_middle; constructor;
    rewrite H2, H3; apply Permutation_split_pivot.
Defined.

Extraction "extraction/qsort.ml" qsort_prog.
