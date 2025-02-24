Require Export Assignment05_28.

(* problem #29: 10 points *)





(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans_sub0 : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  apply H.
  apply le_S.
  apply IHle.
  apply H.
Qed.

