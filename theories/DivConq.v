Require Import Arith List.

(* Below codes are reference and modified from 
   http://adam.chlipala.net/cpdt/html/GeneralRec.html *)

Section DivConq.

Variable A : Type.
Implicit Type l : list A.

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

Lemma lengthOrder_wf : well_founded lengthOrder.
Proof.
red; intro; eapply lengthOrder_wf'; eauto.
Defined.

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

Fixpoint split (ls : list A) : list A * list A :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
        (h1 :: ls1, h2 :: ls2)
  end.

Lemma split_wf : forall len ls, 2 <= length ls <= len
  -> let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.
Proof.
unfold lengthOrder; induction len. sauto. destruct ls. sauto.
destruct ls. sauto. destruct (le_lt_dec 2 (length ls)). sintros; 
specialize (IHlen ls); simpl ; destruct (split ls); destruct IHlen; simpl; sauto.
destruct ls; sauto.
Defined.

Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
  destruct (split ls); destruct 1; sauto.

Lemma split_wf1 : forall ls, 2 <= length ls -> lengthOrder (fst (split ls)) ls.
Proof.
split_wf.
Defined.

Lemma split_wf2 : forall ls, 2 <= length ls -> lengthOrder (snd (split ls)) ls.
Proof.
split_wf.
Defined.

Definition div_conq_split P := div_conq P split split_wf1 split_wf2.

Lemma div_conq_pair : forall (P : list A -> Type),
    P nil -> (forall (a : A), P (a :: nil))
    -> (forall (a1 a2 : A), P (a1 :: a2 :: nil))
    -> (forall (a1 a2 : A) (l : list A), P (a1 :: a2 :: nil) -> P l 
       -> P (a1 :: a2 :: l)) 
    -> forall (l : list A), P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf. sauto.
Defined.

Variable le: A -> A -> Prop.
Variable le_dec: forall (x y: A), {le x y} + {~le x y}.

Fixpoint split_pivot (pivot : A) l : list A * list A :=
  match l with
  | nil => (nil, nil)
  | a :: l' => let (l1, l2) := (split_pivot pivot l') in
    if le_dec a pivot 
    then (a :: l1, l2) else (l1, a :: l2)
  end.

Lemma split_pivot_wf1 : forall a l, length (fst (split_pivot a l)) <= length l.
Proof.
induction l; ssimpl.
Defined.

Lemma split_pivot_wf2 : forall a l, length (snd (split_pivot a l)) <= length l.
Proof.
induction l; ssimpl.
Defined.

Theorem div_conq_pivot : 
  forall (P : list A -> Type),
    P nil
    -> (forall a l, P (fst (split_pivot a l)) -> P (snd (split_pivot a l)) 
      -> P (a :: l))
    -> forall l, P l.
Proof.
intros; eapply well_founded_induction_type. eapply lengthOrder_wf.
destruct x; ssimpl; apply X0; apply X1; unfold lengthOrder; ssimpl; 
apply le_lt_n_Sm. apply split_pivot_wf1. apply split_pivot_wf2.
Defined.

Hypothesis notle_le: forall x y, ~ le x y -> le y x.

Lemma Forall_snd_split_pivot : forall a l, Forall (le a) (snd(split_pivot a l)).
Proof.
induction l; sauto.
Defined.

End DivConq.