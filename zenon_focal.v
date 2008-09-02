(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_focal.v,v 1.1 2008-09-02 12:42:46 pessaux Exp $  *)

Require Export Bool.

Definition __g_not_b := negb.
Definition __g_and_b := andb.
Definition __g_or_b := orb.
Definition __g_xor_b := xorb.
Definition __g_ifthenelse :=
  fun (A:Type) (cond:bool) (x y:A) => if cond then x else y
.

Lemma zenon_focal_false : Is_true false -> False.
Proof.
  unfold Is_true.
  auto.
Qed.

Lemma zenon_focal_nottrue : ~ Is_true true -> False.
Proof.
  unfold Is_true.
  auto.
Qed.

Lemma zenon_focal_falsetrue : false = true -> False.
Proof.
  congruence.
Qed.

Lemma zenon_focal_truefalse : true = false -> False.
Proof.
  congruence.
Qed.

Lemma zenon_focal_not :
 forall a : bool, (~ Is_true a -> False) -> Is_true (__g_not_b a) -> False.
Proof.
  unfold Is_true.
  unfold __g_not_b.
  unfold negb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_notnot :
 forall a : bool, (Is_true a -> False) -> ~ Is_true (__g_not_b a) -> False.
Proof.
  unfold Is_true.
  unfold __g_not_b.
  unfold negb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_and :
 forall a b : bool,
 (Is_true a /\ Is_true b -> False) -> Is_true (__g_and_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_and_b.
  unfold andb.
  unfold ifb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_notand :
 forall a b : bool,
 (~ (Is_true a /\ Is_true b) -> False) -> ~ Is_true (__g_and_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_and_b.
  unfold andb.
  unfold ifb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_or :
 forall a b : bool,
 (Is_true a \/ Is_true b -> False) -> Is_true (__g_or_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_or_b.
  unfold orb.
  unfold ifb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_notor :
 forall a b : bool,
 (~ (Is_true a \/ Is_true b) -> False) -> ~ Is_true (__g_or_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_or_b.
  unfold orb.
  unfold ifb.
  destruct a; tauto.
Qed.

Lemma zenon_focal_xor :
 forall a b : bool,
 (~ (Is_true a <-> Is_true b) -> False) -> Is_true (__g_xor_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_xor_b.
  unfold xorb.
  unfold ifb.
  destruct a; destruct b; tauto.
Qed.

Lemma zenon_focal_notxor :
 forall a b : bool,
 ((Is_true a <-> Is_true b) -> False) -> ~ Is_true (__g_xor_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_xor_b.
  unfold xorb.
  unfold ifb.
  destruct a; destruct b; tauto.
Qed.

Lemma zenon_focal_ite_bool :
  forall cond thn els : bool,
  (Is_true cond -> Is_true thn -> False) ->
  (~Is_true cond -> Is_true els -> False) ->
  Is_true (__g_ifthenelse _ cond thn els) -> False.
Proof.
  intro cond; unfold Is_true; destruct cond; auto.
Qed.

Lemma zenon_focal_ite_bool_n :
  forall cond thn els : bool,
  (Is_true cond -> ~Is_true thn -> False) ->
  (~Is_true cond -> ~Is_true els -> False) ->
  ~Is_true (__g_ifthenelse _ cond thn els) -> False.
Proof.
  intro cond; unfold Is_true; destruct cond; auto.
Qed.

Lemma zenon_focal_ite_rel_l :
  forall (A B : Type) (r: A -> B -> Prop) (cond : bool) (thn els : A) (e2 : B),
  (Is_true cond -> (r thn e2) -> False) ->
  (~Is_true cond -> (r els e2) -> False) ->
  r (__g_ifthenelse _ cond thn els) e2 -> False.
Proof.
  intros A B r cond; unfold Is_true; destruct cond; auto.
Qed.

Implicit Arguments zenon_focal_ite_rel_l [A B].

Lemma zenon_focal_ite_rel_r :
  forall (A B : Type) (r: A -> B -> Prop) (e1 : A) (cond : bool) (thn els : B),
  (Is_true cond -> (r e1 thn) -> False) ->
  (~Is_true cond -> (r e1 els) -> False) ->
  r e1 (__g_ifthenelse _ cond thn els) -> False.
Proof.
  intros A B r e1 cond; unfold Is_true; destruct cond; auto.
Qed.

Implicit Arguments zenon_focal_ite_rel_r [A B].

Lemma zenon_focal_ite_rel_nl :
  forall (A B : Type) (r: A -> B -> Prop) (cond : bool) (thn els : A) (e2 : B),
  (Is_true cond -> ~(r thn e2) -> False) ->
  (~Is_true cond -> ~(r els e2) -> False) ->
  ~(r (__g_ifthenelse _ cond thn els) e2) -> False.
Proof.
  intros A B r cond; unfold Is_true; destruct cond; auto.
Qed.

Implicit Arguments zenon_focal_ite_rel_nl [A B].

Lemma zenon_focal_ite_rel_nr :
  forall (A B : Type) (r: A -> B -> Prop) (e1 : A) (cond : bool) (thn els : B),
  (Is_true cond -> ~(r e1 thn) -> False) ->
  (~Is_true cond -> ~(r e1 els) -> False) ->
  ~(r e1 (__g_ifthenelse _ cond thn els)) -> False.
Proof.
  intros A B r e1 cond; unfold Is_true; destruct cond; auto.
Qed.

Implicit Arguments zenon_focal_ite_rel_nr [A B].

(* ************************************************ *)

Definition zenon_focal_false_s := zenon_focal_false.
Definition zenon_focal_nottrue_s := zenon_focal_nottrue.
Definition zenon_focal_not_s :=
  fun A c h => zenon_focal_not A h c
.
Definition zenon_focal_notnot_s :=
  fun A c h => zenon_focal_notnot A h c
.
Definition zenon_focal_and_s :=
  fun A B c h => zenon_focal_and A B h c
.
Definition zenon_focal_notand_s :=
  fun A B c h => zenon_focal_notand A B h c
.
Definition zenon_focal_or_s :=
  fun A B c h => zenon_focal_or A B h c
.
Definition zenon_focal_notor_s :=
  fun A B c h => zenon_focal_notor A B h c
.
Definition zenon_focal_xor_s :=
  fun A B c h => zenon_focal_xor A B h c
.
Definition zenon_focal_notxor_s :=
  fun A B c h => zenon_focal_notxor A B h c
.
Definition zenon_focal_ite_bool_s :=
  fun i t e c h1 h2 => zenon_focal_ite_bool i t e h1 h2 c
.
Definition zenon_focal_ite_bool_n_s :=
  fun i t e c h1 h2 => zenon_focal_ite_bool_n i t e h1 h2 c
.
Definition zenon_focal_ite_rel_l_s :=
  fun A B r i t e e2 c h1 h2
  => @zenon_focal_ite_rel_l A B r i t e e2 h1 h2 c
.
Implicit Arguments zenon_focal_ite_rel_l_s [A B].
Definition zenon_focal_ite_rel_r_s :=
  fun A B r e1 i t e c h1 h2
  => @zenon_focal_ite_rel_r A B r e1 i t e h1 h2 c
.
Implicit Arguments zenon_focal_ite_rel_r_s [A B].
Definition zenon_focal_ite_rel_nl_s :=
  fun A B r i t e e2 c h1 h2
  => @zenon_focal_ite_rel_nl A B r i t e e2 h1 h2 c
.
Implicit Arguments zenon_focal_ite_rel_nl_s [A B].
Definition zenon_focal_ite_rel_nr_s :=
  fun A B r e1 i t e c h1 h2
  => @zenon_focal_ite_rel_nr A B r e1 i t e h1 h2 c
.
Implicit Arguments zenon_focal_ite_rel_nr_s [A B].
