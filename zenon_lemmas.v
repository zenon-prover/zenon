(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_lemmas.v,v 1.1 2004-05-26 16:23:52 doligez Exp $  *)

Require Import Classical.

(*   (zenon_false H) === H
  Lemma zenon_false :
    (False -> False).
    tauto. Qed.
*)

Lemma zenon_nottrue :
  (~True -> False).
  tauto. Qed.

(*   (zenon_axiom P Q) === (Q P)
   Lemma zenon_axiom : forall P : Prop,
     (P -> ~P -> False).
     tauto. Qed.
*)

Lemma zenon_noteq : forall T : Type, forall t : T,
  ((t <> t) -> False).
  tauto. Qed.

(*   (zenon_notnot P Q) == (Q P)
  Lemma zenon_notnot : forall P : Prop,
    (P -> False) -> (~~P -> False).
    tauto. Qed.
*)

Lemma zenon_and : forall P Q : Prop,
  (P -> Q -> False) -> (P /\ Q -> False).
  tauto. Qed.

Lemma zenon_or : forall P Q : Prop,
  (P -> False) -> (Q -> False) -> (P \/ Q -> False).
  tauto. Qed.

Lemma zenon_imply : forall P Q : Prop,
  (~P -> False) -> (Q -> False) -> ((P -> Q) -> False).
  tauto. Qed.

Lemma zenon_equiv : forall P Q : Prop,
  (~P -> ~Q -> False) -> (P -> Q -> False) -> ((P <-> Q) -> False).
  tauto. Qed.

Lemma zenon_notand : forall P Q : Prop,
  (~P -> False) -> (~Q -> False) -> (~(P /\ Q) -> False).
  tauto. Qed.

Lemma zenon_notor : forall P Q : Prop,
  (~P -> ~Q -> False) -> (~(P \/ Q) -> False).
  tauto. Qed.

Lemma zenon_notimply : forall P Q : Prop,
  (P -> ~Q -> False) -> (~(P -> Q) -> False).
  tauto. Qed.

Lemma zenon_notequiv : forall P Q : Prop,
  (~P -> Q -> False) -> (P -> ~Q -> False) -> (~(P <-> Q) -> False).
  tauto. Qed.

Lemma zenon_ex : forall T : Type, forall P : T -> Prop,
  (forall z : T, ((P z) -> False)) -> ((exists x : T, (P x)) -> False).
  intros T P Ha Hb. elim Hb. auto. Qed.

Lemma zenon_all : forall T : Type, forall P : T -> Prop, forall t : T,
  ((P t) -> False) -> ((forall x : T, (P x)) -> False).
  intros. cut (P t). auto. auto. Qed.

Lemma zenon_notex : forall T : Type, forall P : T -> Prop, forall t : T,
  (~(P t) -> False) -> (~(exists x : T, (P x)) -> False).
  intros T P t Ha Hb. elim Ha. intro. elim Hb. exists t. auto. Qed.

(***** excluded middle is really needed for this one !?! *)
Lemma zenon_notall : forall T : Type, forall P : T -> Prop,
  (forall z : T, (~(P z) -> False)) -> (~(forall x : T, (P x)) -> False).
  intros T P Ha Hb.
  elim Hb.
  intro.
  cut (~ P x -> False).
   intro.
     apply NNPP.
     auto.
     apply (Ha x).
  Qed.

(*
  Lemma zenon_equal_base : forall T : Type, forall f : T, f = f.
    auto. Qed.
*)

Lemma zenon_equal_step :
  forall S T : Type, forall fa fb : S -> T, forall a b : S,
  (fa = fb) -> (a <> b -> False) -> ((fa a) = (fb b)).
  intros S T fa fb a b Ha Hb.
  rewrite Ha.
  rewrite (NNPP (a = b)).
   auto.
   auto.
  Qed.

Lemma zenon_pnotp : forall P Q : Prop,
  (P = Q) -> (P -> ~Q -> False).
  intros P Q Ha. rewrite Ha. auto. Qed.

Lemma zenon_notequal : forall T : Type, forall a b : T,
  (a = b) -> (a <> b -> False).
  auto. Qed.

Lemma zenon_equalnotequal : forall T : Type, forall t u v w : T,
  (t <> v -> u <> v -> False) -> (u <> w -> t <> w -> False)
  -> (t = u -> v <> w -> False).
  intros T t u v w Ha Hb Hc Hd.
  cut (t <> v).
   intro He.
     elim (Ha He).
     rewrite <- Hc.
     auto.
   intro Hf.
     elim Hb.
    rewrite <- Hc.
      rewrite Hf.
      auto.
    rewrite Hf.
      auto.
  Qed.
