Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  destruct m.
  intros.
  split.
  inversion H.
  inversion H.
  intros.
  split.
  apply Sn_le_Sm__n_le_m in H.
  apply n_le_m__Sn_le_Sm.
  apply le_trans with (n:= (n1+n2)).
  apply le_plus_l.
  apply H.
  apply Sn_le_Sm__n_le_m in H.
  apply n_le_m__Sn_le_Sm.
  apply le_trans with (n:= (n1+n2)).
  rewrite plus_comm.
  apply le_plus_l.
  apply H.
Qed.