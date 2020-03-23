Definition lt_nat (n m: nat) : Prop :=
  exists a, n + S a = m.

Definition le_nat (n m: nat) : Prop :=
  lt_nat n (S m).

Theorem nz_pred_exist: forall n,
  n <> 0 -> exists m, n = S m.
Proof.
  intros n Hn.
  destruct n eqn:F.
  - exfalso. apply Hn. reflexivity.
  - exists n0. reflexivity.
Qed.

Theorem le_equal : forall n m,
  le_nat n m <-> exists a, n + a = m.
Proof.
  intros;split;intros.
  - unfold le_nat, lt_nat in H.
    destruct H. 
    rewrite <- plus_n_Sm in H.
    inversion H.
    exists x; auto.
  - destruct H.
    unfold le_nat, lt_nat.
    exists x.
    rewrite <- plus_n_Sm.
    rewrite H; auto.
Qed.
