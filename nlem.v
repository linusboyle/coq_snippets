Theorem nlem: forall p: Prop,
  ~~(p \/ ~p).
Proof.
  intros p.
  intros H.
  apply H.
  right.
  intros S.
  apply H.
  left. apply S.
Qed.
