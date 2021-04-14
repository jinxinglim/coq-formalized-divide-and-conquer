Require Import Arith Sorted Permutation List. 
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

Lemma inserted_sorted : forall (a0 a : nat) (l' x : list nat),
  sorted (a0 :: l') -> sorted x -> permutation x (a :: l') -> a0 < a -> 
  sorted (a0 :: x).
Proof.
intros. constructor.
- trivial.
- apply Sorted_extends in H; (* try hammer *) 
  try strivial use: Nat.lt_le_incl, Nat.le_lt_trans, le_lt_or_eq
  unfold: ge, Relations_1.Transitive.
  assert (H3 : List.Forall (le a0) (a :: l')) by sauto.
  assert (H4 : List.Forall (le a0) x).
  eapply Permutation_Forall. apply Permutation_sym; exact H1. trivial.
  (* hammer *) sauto.
Defined.

Lemma sort_cons_prog : forall (a : nat) (l l' : list nat),
  sorted l' -> permutation l' l -> 
  {l'0 : list nat | sorted l'0 /\ permutation l'0 (a :: l)}.
Proof.
intros.
revert l H H0. induction l'.
- intros. clear H. sauto.
- intros. destruct (IHl' l'); clear IHl'.
  + sauto.
  + sauto.
  + ssimpl. destruct (le_lt_dec a a0).
    * exists (a :: a0 :: l'); sauto.
    * exists (a0 :: x). split.
      -- eapply inserted_sorted; eassumption.
      -- clear H H1 l0; sauto.
Defined.

Lemma isort_prog : 
  forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
Proof.
induction l.
- sauto.
- ssimpl. eapply sort_cons_prog; eassumption.
Defined.

Definition insert_prog (a : nat) (l : list nat) := sort_cons_prog a l l.

Extraction "extraction/insert.ml" insert_prog.
Extraction "extraction/isort.ml" isort_prog.
