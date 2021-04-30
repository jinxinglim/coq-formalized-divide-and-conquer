(* In this file, we will be formalizing different variations of the algorithm
 * paradigm, divide-and-conquer, for lists. Some parts of the codes are
 * referenced and modified from http://adam.chlipala.net/cpdt/html/GeneralRec.html
 * All the variations are derivable from the type, well_founded_induction_type,
 * found in https://coq.inria.fr/library/Coq.Init.Wf.html
 *)

Require Import Arith List.

Section DivConq.

Variable A : Type.
Implicit Type l : list A.


(* (Ordering) lengthOrder ls1 ls2 :=
 * length ls1 < length ls2
 *)

Definition lengthOrder (ls1 ls2 : list A) := length ls1 < length ls2.

Lemma lengthOrder_wf' : forall len, forall ls, 
  length ls <= len -> Acc lengthOrder ls.
Proof.
unfold lengthOrder; induction len.
- intros; rewrite Nat.le_0_r,length_zero_iff_nil in H; rewrite H; constructor;
  intros; inversion H0.
- destruct ls; constructor; simpl; intros.
  + inversion H0.
  + simpl in H; apply le_S_n in H; apply lt_n_Sm_le in H0; apply IHlen; 
    eapply Nat.le_trans; eassumption.
Defined.


(* lengthOrder_wf: 
 * states that the ordering, lengthOrder, is well founded.
 *)

Lemma lengthOrder_wf : well_founded lengthOrder.
Proof.
red; intro; eapply lengthOrder_wf'; eauto.
Defined.


(* div_conq: 
 * Suppose for some arbitrary split function, splitF, with the condition that
 * for any list l, if the length of l is at least 2, then both the sublists
 * generated have length less than the input list. To prove some proposition P
 * holds for all lists ls, one needs to prove the following:
 * 1. P holds for empty list, nil.
 * 2. P holds for one-element list, (a :: nil).
 * 3. If P hold fst(splitF ls) and snd(splitF ls), then P must also hold for ls.
 *)

Lemma div_conq : 
  forall (P : list A -> Type) 
  (splitF : list A -> list A * list A)
  (splitF_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (splitF ls)) ls)
  (splitF_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (splitF ls)) ls),
    P nil -> (forall a, P (a :: nil))
    -> (forall ls, (P (fst (splitF ls)) -> P (snd (splitF ls)) -> P ls))
    -> forall ls, P ls.
Proof.
intros; apply (well_founded_induction_type lengthOrder_wf); intros.
destruct (le_lt_dec 2 (length x)).
- apply X1; apply X2.
  + apply splitF_wf1; auto.
  + apply splitF_wf2; auto.
- destruct x; auto. simpl in l; 
  apply le_S_n, le_S_n, Nat.le_0_r,length_zero_iff_nil  in l; rewrite l; auto.
Defined.


(* split:= 
 * split an input list ls into two sublists where the first sublist contains all
 * the odd indexed element/s and the second sublist contains all the even
 * indexed element/s. 
 *)

Fixpoint split (ls : list A) : list A * list A :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
        (h1 :: ls1, h2 :: ls2)
  end.


(* split_wf: 
 * states that for any list ls of length at least 2, each of the two sublists
 * generated has length less than its original list's.
 *)

Lemma split_wf : forall len ls, 2 <= length ls <= len
  -> let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
Proof.
unfold lengthOrder; induction len; intros.
- inversion H; inversion H1; rewrite H1 in H0; inversion H0.
- destruct ls; inversion H.
  + inversion H0.
  + destruct ls; simpl; auto. 
    destruct (le_lt_dec 2 (length ls)).
    * specialize (IHlen ls); destruct (split ls); destruct IHlen; simpl.
      simpl in H1; apply le_S_n in H1; split; auto. apply le_Sn_le; auto. 
      split; rewrite <- Nat.succ_lt_mono; auto.
    * inversion l. 
      -- destruct ls; inversion H3; apply length_zero_iff_nil in H4; rewrite H4;
         simpl; auto.
      -- apply le_S_n in H3. inversion H3. 
         apply length_zero_iff_nil in H5; rewrite H5; simpl; auto.
Defined.

Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
  destruct (split ls); destruct 1; auto.

Lemma split_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (split ls)) ls.
Proof.
split_wf.
Defined.

Lemma split_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (split ls)) ls.
Proof.
split_wf.
Defined.


(* div_conq_split: 
 * - an instance of div_conq where the arbitrary splitF function
 *   is replaced by the split function defined above.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
     following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. If P hold fst(split ls) and snd(split ls), then P must also hold for ls.
 *)

Definition div_conq_split P := div_conq P split split_wf1 split_wf2.


(* div_conq_pair:
 * - works similar to induction (i.e. list_rect), but instead of cutting just
 *   head of the list in each recursive step, this induction principle cut two
 *   heads of the list in each recursive step.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. P holds for one-element list, (a :: nil).
 *   3. P holds for two-elements list, (a1 :: a2 :: nil).
 *   4. If P hold (a1 :: a2 :: nil) and l, then P must also hold for
 *      (a1 :: a2 :: l).
 *)

Lemma div_conq_pair : forall (P : list A -> Type),
    P nil -> (forall (a : A), P (a :: nil))
    -> (forall (a1 a2 : A), P (a1 :: a2 :: nil))
    -> (forall (a1 a2 : A) (l : list A), P (a1 :: a2 :: nil) -> P l 
       -> P (a1 :: a2 :: l)) 
    -> forall (l : list A), P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
destruct x; auto; destruct x; auto. intros; apply X2; auto.
apply X3; unfold lengthOrder; simpl; auto.
Defined.


Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.


(* split_pivot:= 
 * takes an input term as pivot and list l and split into two sublists where the
 * first sublist contains all element/s that is/are le_dec _ pivot and the
 * second sublist contains the rest of the element/s. 
 *)

Fixpoint split_pivot (pivot : A) l : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' => let (l1, l2) := (split_pivot pivot l') in
    if le_dec a pivot 
    then (a :: l1, l2) else (l1, a :: l2)
  end.


(* split_pivot_wf:
 * states that for any list ls, each of the sublists generated has length less
 * than or equal to its original list's.
 *)

Lemma split_pivot_wf1 : forall a l, length (fst (split_pivot a l)) <= length l.
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l); 
simpl in *; auto; apply le_n_S; auto.
Defined.

Lemma split_pivot_wf2 : forall a l, length (snd (split_pivot a l)) <= length l.
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l); 
simpl in *; auto; apply le_n_S; auto.
Defined.


(* div_conq_pivot:
 * - another variation of div_conq_split, just that for this, it will use 
 *   split_pivot instead.
 * - To prove some proposition P holds for all lists ls, one needs to prove the
 *   following:
 *   1. P holds for empty list, nil.
 *   2. If P hold fst(split_pivot a l) and snd(split_pivot a l), then P must
 *      also hold for (a :: l).
 *)

Theorem div_conq_pivot : 
  forall (P : list A -> Type),
    P nil
    -> (forall a l, P (fst (split_pivot a l)) -> P (snd (split_pivot a l)) 
      -> P (a :: l))
    -> forall l, P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
destruct x; intros; auto; apply X0; apply X1; apply le_lt_n_Sm.
apply split_pivot_wf1. apply split_pivot_wf2.
Defined.



Hypothesis notle_le: forall x y, ~ le x y -> le y x.


(* Forall_snd_split_pivot:
 * le a x for every element, x, in snd(split_pivot a l).
 *)

Lemma Forall_snd_split_pivot : forall a l, Forall (le a) (snd(split_pivot a l)).
Proof.
induction l; simpl; auto; destruct (le_dec a0 a); destruct (split_pivot a l);
simpl in *; auto.
Defined.

End DivConq.