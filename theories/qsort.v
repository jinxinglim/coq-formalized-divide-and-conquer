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

Section PermSplitPivot.

Variable A : Type.
Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.
Implicit Type l : list A.

Lemma Permutation_split_pivot: forall (a : A) l,
  Permutation (fst (split_pivot A le le_dec a l) 
    ++ snd (split_pivot A le le_dec a l)) l.
Proof.
induction l; simpl; auto.
destruct (split_pivot A le le_dec a l); simpl in *.
destruct (le_dec a0 a); simpl; auto;
rewrite <- Permutation_middle; constructor; auto.
Defined.

End PermSplitPivot.

Lemma qsort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
unshelve eapply div_conq_pivot. exact le. exact le_dec.
- exists []; split; constructor.
- intros; destruct H,H0,a0,a1; exists (merge x (a :: x0)); split.
  + apply merge_sorted; auto; constructor; auto.
    assert (Forall (le a) x0).
    eapply Permutation_Forall. apply Permutation_sym; apply H2.
    apply Forall_snd_split_pivot; intros; 
    apply not_le, gt_le_S,le_Sn_le in H3; auto.
    inversion H3; auto.
  + rewrite permutation_merge_concat, <- Permutation_middle; constructor;
    rewrite H0, H2; apply Permutation_split_pivot.
Defined.

(* Extraction "extraction/qsort.ml" qsort_prog. *)
