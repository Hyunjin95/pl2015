Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists [].
  exists l.
  simpl.
  reflexivity.
  inversion IHappears_in.
  exists (b :: witness).
  inversion proof.
  simpl.
  exists witness0.
  rewrite <- proof0.
  reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_here : forall x l, appears_in x l -> repeats (x::l)
  | rep_later : forall x l, repeats l -> repeats (x::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma length_plus_1 {X:Type}: forall (l1: list X) (l2:list X),
  length l1 + S (length l2) = S (length l1 + length l2).
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma appears_in_1 {X:Type}: forall (x0: X) (x: X) (lst:list X),
  appears_in x0 (x::lst) -> x <> x0 -> appears_in x0 lst.
Proof.
  intros.
  unfold not in H0.
  inversion H.
  assert ( x = x0).
  rewrite H2.
  reflexivity.
  apply H0 in H1.
  inversion H1.
  apply H2.
Qed.
  

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros.
   assert (forall (x:X) (l:list X), (appears_in x l) \/ ~ (appears_in x l)).
   intros.
   apply H.
   generalize dependent l2.
   induction l1.
   intros.
   inversion H1.
   intros.
   assert (appears_in x l1 \/ ~ (appears_in x l1)).
   apply H2.
   inversion H3.
   apply rep_here.
   apply H4.
   apply rep_later.
   assert (appears_in x (x :: l1)).
   apply ai_here.
   apply H0 in H5.
   apply appears_in_app_split in H5.
   inversion H5.
   inversion proof.
   rewrite proof0 in H1.
   rewrite app_length in H1.
   simpl in H1.
   rewrite length_plus_1 in H1.
   rewrite <- app_length in H1.
   unfold lt in H1.
   apply Sn_le_Sm__n_le_m in H1.
   assert (forall (n:nat) (m:nat), S n <= m -> n < m).
   intros.
   unfold lt.
   apply H6.
   apply H6 in H1.
   rewrite proof0 in H0.
   apply IHl1 with (l2 := (witness ++ witness0)).
   intros.
   assert (appears_in x0 l1).
   apply H7.
   apply ai_later with (b:= x) in H8.
   apply H0 in H8.
   apply app_appears_in.
   apply appears_in_app in H8.
   inversion H8.
   left.
   apply H9.
   right.
   assert (x <> x0).
   unfold not.
   intros.
   rewrite H10 in H4.
   apply H4 in H7.
   apply H7.
   apply appears_in_1 in H9.
   apply H9.
   apply H10.
   apply H1.
Qed.
   