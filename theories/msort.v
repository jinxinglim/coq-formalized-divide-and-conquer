Require Import Arith Sorted Permutation List DivConq. 
Import List.ListNotations.
Open Scope list_scope.

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
- constructor. apply IHl1; inversion H; auto.
  destruct l1; destruct l2; simpl; auto; destruct (le_lt_dec n a0); auto;
  constructor; inversion H; inversion H4; auto.
- constructor. inversion H0; apply IHl2; auto.
  destruct l2. constructor; apply Nat.lt_le_incl; auto. 
  destruct (le_lt_dec a n); constructor; inversion H0; inversion H4; auto;
  apply Nat.lt_le_incl; auto.
Defined.

Lemma permutation_merge_concat : forall (l1 l2 : list nat),
  permutation (merge l1 l2) (l1 ++ l2).
Proof.
induction l1; simpl merge.
- destruct l2; apply Permutation_refl.
- induction l2.
  + rewrite <- app_nil_end; apply Permutation_refl.
  + destruct (le_lt_dec a a0).
    * constructor; apply IHl1.
    * apply Permutation_cons_app, IHl2.
Defined.

Lemma permutation_split : forall (l : list nat),
  permutation (fst (split nat l) ++ snd (split nat l)) l.
Proof.
apply div_conq_pair; intros; simpl.
- constructor.
- repeat constructor.
- repeat constructor.
- destruct (split nat l); simpl in *; constructor;
  apply Permutation_sym,Permutation_cons_app, Permutation_sym; auto.
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
- exists []; split; constructor.
- intros; exists [a]; split; constructor; constructor.
- intros; destruct H; destruct a; destruct H0; destruct a;
  eapply merge_prog. apply H. trivial. apply H0. trivial. 
Defined.

Extraction "extraction/merge.ml" merge.
Extraction "extraction/msort.ml" msort_prog.
