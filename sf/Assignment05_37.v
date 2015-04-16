Require Export Assignment05_36.

(* problem #37: 10 points *)

Lemma bleble : forall n,
  ble_nat n n = true.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.

Lemma blebleble : forall n m,
  ble_nat n m = true -> ble_nat n (S m) = true.
Proof.
  intros.
  generalize dependent m.
  induction n.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  inversion H.
  destruct m.
  inversion H.
  rewrite H1.
  apply IHn.
  apply H1.
Qed.
  
  

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  intros.
  generalize dependent n.
  induction m.
  intros.
  inversion H.
  simpl.
  reflexivity.
  intros.
  inversion H.
  simpl.
  apply bleble.
  apply IHm in H2.
  apply blebleble.
  apply H2.
Qed.

