(*  Copyright 2004 INRIA  *)
(*  $Id: zenon8.v,v 1.3 2004-10-18 16:53:28 doligez Exp $  *)

Require Export Classical.

Lemma zenon_nottrue :
  (~True -> False).
  tauto. Qed.

Lemma zenon_noteq : forall (T : Type) (t : T),
  ((t <> t) -> False).
  tauto. Qed.

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

Lemma zenon_ex : forall (T : Type) (P : T -> Prop),
  (forall z : T, ((P z) -> False)) -> ((exists x : T, (P x)) -> False).
  intros T P Ha Hb. elim Hb. auto. Qed.

Lemma zenon_all : forall (T : Type) (P : T -> Prop) (t : T),
  ((P t) -> False) -> ((forall x : T, (P x)) -> False).
  intros. cut (P t). auto. auto. Qed.

Lemma zenon_notex : forall (T : Type) (P : T -> Prop) (t : T),
  (~(P t) -> False) -> (~(exists x : T, (P x)) -> False).
  intros T P t Ha Hb. elim Ha. intro. elim Hb. exists t. auto. Qed.

(***** excluded middle is really needed for this one !?! *)
Lemma zenon_notall : forall (T : Type) (P : T -> Prop),
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

Lemma zenon_equal_base : forall (T : Type) (f : T), f = f.
  auto. Qed.

Lemma zenon_equal_step :
  forall (S T : Type) (fa fb : S -> T) (a b : S),
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

Lemma zenon_notequal : forall (T : Type) (a b : T),
  (a = b) -> (a <> b -> False).
  auto. Qed.

Lemma zenon_equalnotequal : forall (T : Type) (t u v w : T),
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

Ltac cintro id := intro id || let nid := fresh in (intro nid; clear nid).

Definition zenons_imply := fun P Q a b c => zenon_imply P Q b c a.
Definition zenons_equiv := fun P Q a b c => zenon_equiv P Q b c a.
Definition zenons_notand := fun P Q a b c => zenon_notand P Q b c a.
Definition zenons_notor := fun P Q a b => zenon_notor P Q b a.
Definition zenons_notimply := fun P Q a b => zenon_notimply P Q b a.
Definition zenons_notequiv := fun P Q a b c => zenon_notequiv P Q b c a.
Definition zenons_equalnotequal :=
  fun T t u v w a b c d => zenon_equalnotequal T t u v w c d a b
.
Definition zenons_pnotp := fun P Q a b c => zenon_pnotp P Q c a b.
Definition zenons_notequal := fun T a b x y => zenon_notequal T a b y x.
