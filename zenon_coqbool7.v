(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_coqbool7.v,v 1.1 2004-09-09 15:25:36 doligez Exp $  *)

Require Import Bool.

Definition __g_not_b := negb.
Definition __g_and_b := andb.
Definition __g_or_b := orb.
Definition __g_xor_b := xorb.

Theorem zenon_coqbool_false : (Is_true false) -> False.
Proof.
  Unfold Is_true.
  Auto.
Qed.

Theorem zenon_coqbool_nottrue : ~ (Is_true true) -> False.
Proof.
  Unfold Is_true.
  Auto.
Qed.

Theorem zenon_coqbool_not : (a : bool)
  (~(Is_true a) -> False) -> (Is_true (__g_not_b a)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_not_b.
  Unfold negb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_notnot : (a : bool)
  ((Is_true a) -> False) -> (~ (Is_true (__g_not_b a))) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_not_b.
  Unfold negb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_and : (a : bool) (b : bool)
  ((and (Is_true a) (Is_true b)) -> False)
  -> (Is_true (__g_and_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_and_b.
  Unfold andb.
  Unfold ifb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_notand : (a : bool) (b : bool)
  (~(and (Is_true a) (Is_true b)) -> False)
  -> ~(Is_true (__g_and_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_and_b.
  Unfold andb.
  Unfold ifb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_or : (a : bool) (b : bool)
  ((or (Is_true a) (Is_true b)) -> False)
  -> (Is_true (__g_or_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_or_b.
  Unfold orb.
  Unfold ifb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_notor : (a : bool) (b : bool)
  (~(or (Is_true a) (Is_true b)) -> False)
  -> ~(Is_true (__g_or_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_or_b.
  Unfold orb.
  Unfold ifb.
  NewDestruct a; Tauto.
Qed.

Theorem zenon_coqbool_xor : (a : bool) (b : bool)
  (~((Is_true a) <-> (Is_true b)) -> False)
  -> (Is_true (__g_xor_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_xor_b.
  Unfold xorb.
  Unfold ifb.
  NewDestruct a; NewDestruct b; Tauto.
Qed.

Theorem zenon_coqbool_notxor : (a : bool) (b : bool)
  (((Is_true a) <-> (Is_true b)) -> False)
  -> ~(Is_true (__g_xor_b a b)) -> False.
Proof.
  Unfold Is_true.
  Unfold __g_xor_b.
  Unfold xorb.
  Unfold ifb.
  NewDestruct a; NewDestruct b; Tauto.
Qed.
