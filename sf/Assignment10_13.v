Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  unfold par_loop.
  induction n;
  intros.
  exists st.
  split.
  apply multi_refl.
  apply H.
  assert (exists st' : state,
        (par_loop / st ==>c* par_loop / st') /\ (st' X = n /\ st' Y = 0)).
  apply IHn.
  apply H.
  inversion H0.
  exists (update x X (S n)).
  split;
  inversion H1.
  eapply multi_trans.
  apply H2.
  eapply par_body_n__Sn.
  apply H3.
  split.
  rewrite update_eq.
  reflexivity.
  rewrite update_neq.
  inversion H3.
  apply H5.
  destruct (eq_id_dec X Y) eqn:xy.
  inversion xy.
  apply n0.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

