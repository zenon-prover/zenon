(*  Copyright 2004 INRIA  *)
(*  $Id: zenon.v,v 1.1 2004-05-27 17:21:24 doligez Exp $  *)

Require Import Classical.

(*   (zenon_false H) === H
  Lemma zenon_false :
    (False -> False).
    Tauto. Qed.
*)

Lemma zenon_nottrue :
  (~True -> False).
  Tauto. Qed.

(*   (zenon_axiom P Q) === (Q P)
   Lemma zenon_axiom : forall P : Prop,
     (P -> ~P -> False).
     Tauto. Qed.
*)

Lemma zenon_noteq : (T : Type) (t : T)
  ((t <> t) -> False).
  Tauto. Qed.

(*   (zenon_notnot P Q) == (Q P)
  Lemma zenon_notnot : forall P : Prop,
    (P -> False) -> (~~P -> False).
    Tauto. Qed.
*)

Lemma zenon_and : (P : Prop) (Q : Prop)
  (P -> Q -> False) -> (P /\ Q -> False).
  Tauto. Qed.

Lemma zenon_or : (P : Prop) (Q : Prop)
  (P -> False) -> (Q -> False) -> (P \/ Q -> False).
  Tauto. Qed.

Lemma zenon_imply : (P : Prop) (Q : Prop)
  (~P -> False) -> (Q -> False) -> ((P -> Q) -> False).
  Tauto. Qed.

Lemma zenon_equiv : (P : Prop) (Q : Prop)
  (~P -> ~Q -> False) -> (P -> Q -> False) -> ((P <-> Q) -> False).
  Tauto. Qed.

Lemma zenon_notand : (P : Prop) (Q : Prop)
  (~P -> False) -> (~Q -> False) -> (~(P /\ Q) -> False).
  Tauto. Qed.

Lemma zenon_notor : (P : Prop) (Q : Prop)
  (~P -> ~Q -> False) -> (~(P \/ Q) -> False).
  Tauto. Qed.

Lemma zenon_notimply : (P : Prop) (Q : Prop)
  (P -> ~Q -> False) -> (~(P -> Q) -> False).
  Tauto. Qed.

Lemma zenon_notequiv : (P : Prop) (Q : Prop)
  (~P -> Q -> False) -> (P -> ~Q -> False) -> (~(P <-> Q) -> False).
  Tauto. Qed.

Lemma zenon_ex : (T : Type) (P : T -> Prop)
  ((z : T) ((P z) -> False)) -> ((Ex [x : T] (P x)) -> False).
  Intros T P Ha Hb. Elim Hb. Auto. Qed.

Lemma zenon_all : (T : Type) (P : T -> Prop) (t : T)
  ((P t) -> False) -> (((x : T) (P x)) -> False).
  Intros. Cut (P t). Auto. Auto. Qed.

Lemma zenon_notex : (T : Type) (P : T -> Prop) (t : T)
  (~(P t) -> False) -> (~(Ex [x : T] (P x)) -> False).
  Intros T P t Ha Hb. Elim Ha. Intro. Elim Hb. Exists t. Auto. Qed.

(***** excluded middle is really needed for this one !?! *)
Lemma zenon_notall : (T : Type) (P : T -> Prop)
  ((z : T) (~(P z) -> False)) -> (~((x : T) (P x)) -> False).
  Intros T P Ha Hb.
  Elim Hb.
  Intro.
  Cut (~ (P x) -> False).
   Intro.
     Apply NNPP.
     Auto.
     Apply (Ha x).
  Qed.

(*
  Lemma zenon_equal_base : (T : Type) (f : T) f = f.
    Auto. Qed.
*)

Lemma zenon_equal_step :
  (S : Type) (T : Type) (fa : S -> T) (fb : S -> T) (a : S) (b : S)
  (fa = fb) -> (a <> b -> False) -> ((fa a) = (fb b)).
  Intros S T fa fb a b Ha Hb.
  Rewrite Ha.
  Rewrite (NNPP (a = b)).
   Auto.
   Auto.
  Qed.

Lemma zenon_pnotp : (P : Prop) (Q : Prop)
  (P = Q) -> (P -> ~Q -> False).
  Intros P Q Ha. Rewrite Ha. Auto. Qed.

Lemma zenon_notequal : (T : Type) (a  : T) (b : T)
  (a = b) -> (a <> b -> False).
  Auto. Qed.

Lemma zenon_equalnotequal : (T : Type) (t : T) (u : T) (v : T) (w : T)
  (t <> v -> u <> v -> False) -> (u <> w -> t <> w -> False)
  -> (t = u -> v <> w -> False).
  Intros T t u v w Ha Hb Hc Hd.
  Cut (t <> v).
   Intro He.
     Elim (Ha He).
     Rewrite <- Hc.
     Auto.
   Intro Hf.
     Elim Hb.
    Rewrite <- Hc.
      Rewrite Hf.
      Auto.
    Rewrite Hf.
      Auto.
  Qed.
