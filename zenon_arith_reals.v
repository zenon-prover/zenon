
Require Export Reals.
Require Import Psatz.

Open Scope R.

Ltac real_const := lra.

Lemma arith_real_eq : forall a b: R, a = b -> a <= b /\ a >= b.
Proof. intros. lra. Qed.

Lemma arith_real_neq : forall a b: R, (~ a = b) -> a < b \/ a > b.
Proof. intros. lra. Qed.

Lemma arith_real_neg_leq : forall a b: R, (~ a <= b) -> a > b.
Proof. intros. exact (Rnot_le_gt _ _ H). Qed.

Lemma arith_real_neg_lt : forall a b: R, (~ a < b) -> a >= b.
Proof. intros. exact (Rnot_lt_ge _ _ H). Qed.

Lemma arith_real_neg_geq : forall a b: R, (~ a >= b) -> a < b.
Proof. intros. exact (Rnot_ge_lt _ _ H). Qed.

Lemma arith_real_neg_gt : forall a b: R, (~ a > b) -> a <= b.
Proof. intros. exact (Rnot_gt_le _ _ H). Qed.
