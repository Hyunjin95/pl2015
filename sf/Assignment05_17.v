Require Export Assignment05_16.

(* problem #17: 10 points *)





(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   intros.
   induction m.
   induction n.
   simpl.
   apply H.
   simpl.
   constructor 1.
   simpl.
   constructor 4.
   apply H.
   apply IHm.
Qed.
(** [] *)




