(*  Copyright 2008 INRIA  *)
(*  $Id: zenon_inductive.v,v 1.2 2008-11-24 15:28:27 doligez Exp $  *)

Lemma zenon_inductive_match_redex : forall A : Prop, Prop ->
  (A -> False) -> (A -> False).
  Proof. tauto. Qed.

Definition zenon_inductive_match_redex_s :=
  fun A B c h => zenon_inductive_match_redex A B h c
.

Lemma zenon_inductive_f_equal : forall (T1 T2 : Type) (x y : T1) (f : T1 -> T2),
  (f x = f y -> False) -> (x = y -> False).
  Proof. intros T1 T2 x y f H1 H2. apply H1. subst x. auto. Qed.

Implicit Arguments zenon_inductive_f_equal [T1 T2].

Definition zenon_inductive_f_equal_s :=
  fun t1 t2 x y f c h => @zenon_inductive_f_equal t1 t2 x y f h c
.

Implicit Arguments zenon_inductive_f_equal_s [t1 t2].

Lemma zenon_inductive_ex_all : forall (T : Type) (P : T -> Prop),
  ((exists x, P(x)) -> False) -> forall x, (P(x) -> False).
  Proof. firstorder. Qed.

Lemma zenon_inductive_eq_and : forall (T : Type) (e : T) P,
  (e = e /\ P -> False) -> P -> False.
  Proof. firstorder. Qed.
