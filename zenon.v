(*  Copyright 2004 INRIA  *)
(*  $Id: zenon.v,v 1.4 2005-11-05 11:13:17 doligez Exp $  *)

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

Lemma zenon_eqnoteq : forall (T : Type) (a b c d : T),
  (a <> c -> False) -> (b <> d -> False) -> (a = b -> c <> d -> False).
  intros T a b c d Hac Hbd e ne.
  apply Hac; intro.
  apply Hbd; intro.
  apply ne.
  congruence.
  Qed.

Lemma zenon_notequal : forall (T : Type) (a b : T),
  (a = b) -> (a <> b -> False).
  auto. Qed.

Ltac cintro id := intro id || let nid := fresh in (intro nid; clear nid).

Definition zenon_imply_s := fun P Q a b c => zenon_imply P Q b c a.
Definition zenon_equiv_s := fun P Q a b c => zenon_equiv P Q b c a.
Definition zenon_notand_s := fun P Q a b c => zenon_notand P Q b c a.
Definition zenon_notor_s := fun P Q a b => zenon_notor P Q b a.
Definition zenon_notimply_s := fun P Q a b => zenon_notimply P Q b a.
Definition zenon_notequiv_s := fun P Q a b c => zenon_notequiv P Q b c a.
Definition zenon_pnotp_s := fun P Q a b c => zenon_pnotp P Q c a b.
Definition zenon_eqnoteq_s :=
   fun T a b c d x y z t => zenon_eqnoteq T a b c d z t x y
.
Definition zenon_notequal_s := fun T a b x y => zenon_notequal T a b y x.
