Require Import List.

Fixpoint take_impl {A : Type} (ll lr: list A) (n: nat) : list A * nat :=
  match n with
  | O => (ll, O)
  | S n' => 
      match lr with
      | nil => (ll, O)
      | h :: t =>
          take_impl (ll ++ (h :: nil)) t n' 
      end
  end.

Definition take {A : Type} (n : nat) (l: list A) :=
  let (l', _) := take_impl nil l n in
  l'.

Definition init {A : Type} (l : list A) :=
  take (pred (length l)) l.

Fixpoint foldl {A : Type} (f : A -> A -> A) (x0 : A) (d: list A) :=
  match d with
  | nil => x0
  | h :: t => 
      let a := f x0 h in
      foldl f a t
  end.
