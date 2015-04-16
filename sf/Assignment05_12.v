Require Export Assignment05_11.

(* problem #12: 10 points *)

Lemma o_o :
 0 = 0.
Proof. auto. Qed.



(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  induction n.
  induction m.
  simpl.
  intros.
  unfold not in H.
  assert (0=0).
  reflexivity.
  apply H in H0.
  inversion H0.
  simpl.
  reflexivity.
  simpl.
  destruct m.
  reflexivity.
  intros.
  apply IHn.
  unfold not in H.
  unfold not.
  intros.
  apply H.
  apply f_equal.
  apply H0.
Qed.
(** [] *)




