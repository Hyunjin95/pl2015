Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 intros.
 induction H.
 constructor 1.
 constructor 2.
 constructor 1.
 constructor 3.
 constructor 1.
 apply gorgeous_sum.
 apply IHbeautiful1.
 apply IHbeautiful2.
Qed.
(** [] *)




