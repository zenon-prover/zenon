(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_coqbool.v,v 1.1 2004-05-27 17:21:24 doligez Exp $  *)

Require Import Bool.

Definition __g_not_b := negb.

Lemma if_negb_T : (T : Type) (b : bool) (x : T) (y : T)
  (if (negb b) then x else y) = (if b then y else x).
Proof.
  Destruct b.
   Trivial.
   Trivial.
Qed.

Theorem zenon_coqbool_not : (e : bool)
  (~(Is_true e) -> False) -> (Is_true (__g_not_b e)) -> False.
Proof.
  Intro.
  Intro.
  Intro.
  Cut (~ (Is_true (negb e))).
   Unfold Is_true.
     Intro.
     Elim H1.
     NewDestruct e.
    Trivial.
    Trivial.
   Unfold Is_true.
     Intro.
     Elim H.
     Unfold Is_true.
     Intro.
     Auto.
     Rewrite (if_negb_T Prop e True False) in H1.
     Cut (e = true).
    Intro.
      Rewrite H3 in H1.
      Auto.
    Apply not_false_is_true.
      Intro.
      Rewrite H3 in H2.
      Auto.
Qed.
