Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)
Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros.
  induction n.
  split.
  intros.
  constructor 1.
  intros.
  constructor 1.
  inversion IHn.
  split.
  intros.
  simpl in H1.
  simpl.
  apply IHn in H1.
  apply H1.
  intros.
  inversion H1.
  destruct n.
  inversion H3.
  simpl in H.
  unfold even in H.
  constructor 2.
  apply H in H3.
  apply H3.
Qed.
(** [] *)

