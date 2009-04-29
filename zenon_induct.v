(*  Copyright 2008 INRIA  *)
(*  $Id: zenon_induct.v,v 1.3 2009-04-29 12:07:04 doligez Exp $  *)

Lemma zenon_induct_match_redex : forall A : Prop,
  (A -> False) -> (A -> False).
  Proof. tauto. Qed.

Definition zenon_induct_match_redex_s :=
  fun A c h => zenon_induct_match_redex A h c
.

Lemma zenon_induct_f_equal : forall (T1 T2 : Type) (x y : T1) (f : T1 -> T2),
  (f x = f y -> False) -> (x = y -> False).
  Proof. intros T1 T2 x y f H1 H2. apply H1. subst x. auto. Qed.

Implicit Arguments zenon_induct_f_equal [T1 T2].

Definition zenon_induct_f_equal_s :=
  fun t1 t2 x y f c h => @zenon_induct_f_equal t1 t2 x y f h c
.

Implicit Arguments zenon_induct_f_equal_s [t1 t2].

Lemma zenon_induct_case_subs : forall (T : Type) (b a : T) P,
  (b = a -> P(a) -> False) -> b = a -> P(b) -> False.
  Proof. intros T b a P H e pa. subst b. apply H; auto. Qed.

(*
Lemma zenon_induct_ex_all : forall (T : Type) (P : T -> Prop),
  ((exists x : T, P(x)) -> False) -> forall x : T, P(x) -> False.
  Proof. firstorder. Qed.
*)

Lemma zenon_nnnpnp : forall P : Prop, (~~P -> False) -> P -> False.
  Proof. tauto. Qed.
