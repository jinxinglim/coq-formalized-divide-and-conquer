Require Import Arith Sorted Permutation List DivConq. 
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

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if (le_lt_dec a1 a2) then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Lemma merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
induction l1; induction l2; intros; simpl; auto.
destruct (le_lt_dec a a0).
- constructor. apply IHl1; sauto. sauto.
- constructor; sauto.
Defined.

Lemma permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).
Proof.
induction l1; simpl merge.
- sauto.
- induction l2.
  + (* hammer. *)
    hauto use: app_nil_l, Permutation_middle, app_comm_cons, app_nil_end 
    unfold: permutation.
  + destruct (le_lt_dec a a0).
    * sauto.
    * apply Permutation_cons_app, IHl2.
Defined.

Lemma permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.
Proof.
apply div_conq_pair; ssimpl; constructor; clear H;
apply Permutation_sym; apply Permutation_cons_app; (* try hammer. *)
srun eauto use: Permutation_sym unfold: permutation.
Defined.

Lemma merge_prog : forall (l l1 l2 : list nat), 
  sorted l1 -> permutation l1 (fst (split nat l)) ->
  sorted l2 -> permutation l2 (snd (split nat l)) ->
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
intros; exists (merge l1 l2); split.
  + apply merge_sorted; eassumption.
  + rewrite permutation_merge_concat, H0, H2; apply permutation_split.
Defined.

Lemma msort_prog : forall (l : list nat), 
  {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
apply div_conq_split. 
- sauto.
- sauto.
- ssimpl; eapply merge_prog. apply H0. trivial. apply H1. trivial. 
Defined.

Extraction "extraction/merge.ml" merge.
Extraction "extraction/msort.ml" msort_prog.
