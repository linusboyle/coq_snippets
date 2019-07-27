Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Permutation.

Fixpoint insert (a: nat) (l: list nat): list nat :=
  match l with
  | nil => a :: nil
  | h :: t => if a <=? h then a :: h :: t
              else h :: (insert a t)
  end.

Fixpoint insertion_sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Inductive sorted : list nat -> Prop :=
  |sorted_nil: sorted nil
  |sorted_sin: forall a,
      sorted (a :: nil)
  |sorted_ite: forall x y l',
      x <= y ->
      sorted (y :: l') ->
      sorted (x :: y :: l')
.

Lemma insert_sorted:
  forall a l, sorted l->
  sorted (insert a l).
Proof.
  intros.
  induction H;simpl.
  - apply sorted_sin.
  - destruct (a <=? a0) eqn:E.
    + rewrite Nat.leb_le in E.
      apply sorted_ite;try assumption.
      apply sorted_sin.
    + rewrite Nat.leb_nle in E.
      apply sorted_ite.
      omega.
      apply sorted_sin.
  - destruct (a <=? x) eqn:E.
    + rewrite Nat.leb_le in E.
      apply sorted_ite;try assumption.
      apply sorted_ite;try assumption.
    + rewrite Nat.leb_nle in E.
      destruct (a <=? y) eqn:F.
      * rewrite Nat.leb_le in F.
        apply sorted_ite;try omega.
        apply sorted_ite;try omega.
        assumption.
      * simpl in IHsorted.
        rewrite F in IHsorted.
        apply sorted_ite;[omega|assumption].
Qed.

Lemma insertion_sort_sorted:
  forall l, sorted (insertion_sort l).
Proof.
  intros l.
  induction l.
  - simpl. constructor.
  - simpl.
    apply insert_sorted. assumption.
Qed.

Lemma insert_permutation:
  forall a l, Permutation (a :: l) (insert a l).
Proof.
  intros a l.
  induction l.
  - simpl. repeat constructor.
  - simpl.
    destruct (a <=? a0) eqn:E.
    + repeat constructor. 
      apply Permutation_refl.
    + eapply perm_trans.
      apply perm_swap.
      constructor. assumption.
Qed.

Lemma insertion_sort_permutation:
  forall l, Permutation l (insertion_sort l).
Proof.
  induction l.
  - constructor.
  - simpl.
    eapply perm_trans. 
    2: apply insert_permutation.
    constructor. assumption.
Qed.

Theorem insertion_sort_correct:
  forall l, let sl := insertion_sort l in
    sorted sl /\ Permutation l sl.
Proof.
  intros l.
  simpl.
  split;[apply insertion_sort_sorted|apply insertion_sort_permutation].
Qed.
