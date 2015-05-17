Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma APlus_congruence : forall a1 a1' a2 a2',
  aequiv a1 a1' ->
  aequiv a2 a2' ->
  aequiv (APlus a1 a2) (APlus a1' a2').
Proof.
  intros. unfold aequiv in *. intros.
  simpl. auto.
Qed.

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  intros a st.
  aexp_cases (induction a) Case; simpl;
  try reflexivity; try (rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

