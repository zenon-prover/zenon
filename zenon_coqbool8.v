(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_coqbool8.v,v 1.1 2004-09-09 15:25:36 doligez Exp $  *)

Require Import Bool.

Definition __g_not_b := negb.
Definition __g_and_b := andb.
Definition __g_or_b := orb.
Definition __g_xor_b := xorb.

Theorem zenon_coqbool_false : Is_true false -> False.
Proof.
  unfold Is_true.
  auto.
Qed.

Theorem zenon_coqbool_nottrue : ~ Is_true true -> False.
Proof.
  unfold Is_true.
  auto.
Qed.

Theorem zenon_coqbool_not :
 forall a : bool, (~ Is_true a -> False) -> Is_true (__g_not_b a) -> False.
Proof.
  unfold Is_true.
  unfold __g_not_b.
  unfold negb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_notnot :
 forall a : bool, (Is_true a -> False) -> ~ Is_true (__g_not_b a) -> False.
Proof.
  unfold Is_true.
  unfold __g_not_b.
  unfold negb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_and :
 forall a b : bool,
 (Is_true a /\ Is_true b -> False) -> Is_true (__g_and_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_and_b.
  unfold andb.
  unfold ifb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_notand :
 forall a b : bool,
 (~ (Is_true a /\ Is_true b) -> False) -> ~ Is_true (__g_and_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_and_b.
  unfold andb.
  unfold ifb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_or :
 forall a b : bool,
 (Is_true a \/ Is_true b -> False) -> Is_true (__g_or_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_or_b.
  unfold orb.
  unfold ifb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_notor :
 forall a b : bool,
 (~ (Is_true a \/ Is_true b) -> False) -> ~ Is_true (__g_or_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_or_b.
  unfold orb.
  unfold ifb.
  destruct a; tauto.
Qed.

Theorem zenon_coqbool_xor :
 forall a b : bool,
 (~ (Is_true a <-> Is_true b) -> False) -> Is_true (__g_xor_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_xor_b.
  unfold xorb.
  unfold ifb.
  destruct a; destruct b; tauto.
Qed.

Theorem zenon_coqbool_notxor :
 forall a b : bool,
 ((Is_true a <-> Is_true b) -> False) -> ~ Is_true (__g_xor_b a b) -> False.
Proof.
  unfold Is_true.
  unfold __g_xor_b.
  unfold xorb.
  unfold ifb.
  destruct a; destruct b; tauto.
Qed.
