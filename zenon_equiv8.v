(*  Copyright 2004 INRIA  *)
(*  $Id: zenon_equiv8.v,v 1.1 2004-10-18 16:53:28 doligez Exp $  *)

Lemma zenon_equiv_init_0 : forall A : Prop,
  ((True <-> (A <-> True)) -> False) -> A -> False.
  tauto. Qed.

Lemma zenon_equiv_init_1 : forall K A B : Prop,
  (((K <-> (True <-> A)) <-> B) -> False) -> (K <-> (A <-> B)) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_2 : forall K A B C : Prop,
  ((K <-> (A <-> (B <-> C))) -> False) -> (K <-> ((A <-> B) <-> C)) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_3 : forall K A B : Prop,
  ((K <-> (A <-> ~B)) -> False) -> (K <-> ~(A <-> B)) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_4 : forall K A : Prop,
  ((K <-> A) -> False) -> (K <-> ~~A) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_5 : forall K A B : Prop,
  ((K <-> (A <-> ~B)) -> False) -> (K <-> (~A <-> B)) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_6 : forall K : Prop,
  (((K <-> True) <-> (True <-> True)) -> False) -> (K <-> True) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_7 : forall K : Prop,
  (((K <-> True) <-> (False <-> True)) -> False) -> (K <-> ~True) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_8 : forall K B : Prop,
  ((K <-> B) -> False) -> (K <-> (True <-> B)) -> False.
  tauto. Qed.

Lemma zenon_equiv_init_9 : forall K B : Prop,
  ((K <-> ~B) -> False) -> (K <-> (False <-> B)) -> False.
  tauto. Qed.

Lemma zenon_equiv_merge_right : forall X D E F G : Prop,
  (((X <-> D) <-> (F <-> (G <-> E))) -> False)
  -> ((X <-> (D <-> E)) <-> (F <-> G))
  -> False.
  tauto. Qed.

Lemma zenon_equiv_merge_left : forall A B C Y F G : Prop,
  ((((A <-> B) <-> Y) <-> (F <-> (G <-> C))) -> False)
  -> (((A <-> (B <-> C)) <-> Y) <-> (F <-> G))
  -> False.
  tauto. Qed.

Lemma zenon_equiv_merge_1 : forall A L Q : Prop,
  ((A <-> ((Q <-> L) <-> True)) -> False)
  -> ((A <-> L) <-> (Q <-> True))
  -> False.
  tauto. Qed.

Lemma zenon_equiv_simplify : forall A L M N : Prop,
  ((L <-> (M <-> N)) -> False) -> (L <-> (M <-> ((N <-> A) <-> A))) -> False.
  tauto. Qed.

Lemma zenon_equiv_merge_simplify : forall A B C D Z : Prop,
  ((((A <-> B) <-> D) <-> Z) -> False)
  -> (((A <-> (B <-> C)) <-> (D <-> C)) <-> Z)
  -> False.
  tauto. Qed.

Lemma zenon_equiv_inner_loop : forall L A B : Prop,
  ((L <-> ((A <-> True) <-> B)) -> False)
  -> (((L <-> True) <-> True) <-> (A <-> B))
  -> False.
  tauto. Qed.

Lemma zenon_equiv_reverse : forall L A B C D : Prop,
  ((L <-> ((A <-> (B <-> D)) <-> C)) -> False)
  -> (L <-> ((A <-> B) <-> (C <-> D)))
  -> False.
  tauto. Qed.

Lemma zenon_equiv_outer_loop : forall A Q : Prop,
  ((Q <-> (A <-> True)) -> False) -> (A <-> (Q <-> True)) -> False.
  tauto. Qed.

Lemma zenon_equiv_finish_0 : forall Q : Prop,
  (Q -> False) -> (True <-> ((True <-> Q) <-> True)) -> False.
  tauto. Qed.

Lemma zenon_equiv_finish_1 : forall Q : Prop,
  (~Q -> False) -> (True <-> ((False <-> Q) <-> True)) -> False.
  tauto. Qed.

Lemma zenon_equiv_finish_2 : forall Q : Prop,
  (~Q -> False) -> (False <-> ((True <-> Q) <-> True)) -> False.
  tauto. Qed.
