
Require Export Reals.
Require Import Psatz.

Open Scope R.

Lemma Rplus_inj : forall r r1 r2: R, r1 = r2 <-> r + r1 = r + r2.
Proof.
intros. split.
  - intro. exact (Rplus_eq_compat_l r r1 r2 H).
  - intro. exact (Rplus_eq_reg_l r r1 r2 H).
Qed.

Ltac real_const := lra.

Ltac real_norm :=
  match goal with
  | |- ?a =  ?b => rewrite -> (Rplus_inj (- b) _ _)
  | |- ?a <= ?b => rewrite -> (Rplus_inj (- b) _ _)
  | |- ?a <  ?b => rewrite -> (Rplus_inj (- b) _ _)
  end;
  ring_simplify.

Ltac real_norm_in H :=
  match type of H with
  | ?a = ?b => rewrite -> (Rplus_inj (- b) _ _) in H
  | ?a <= ?b => rewrite -> (Rplus_inj (- b) _ _) in H
  | ?a <  ?b => rewrite -> (Rplus_inj (- b) _ _) in H
  end;
  ring_simplify in H.

Ltac real_simpl k H :=
  try (rewrite (Rmult_eq_compat_r _ _ k) in H; [ idtac | real_const ]);
  real_norm; real_norm_in H;
  match goal with
  | H: ?e <= 0 |- ?f <= 0 =>
      let x := fresh in
      cut (e = f); [
        intro x; try rewrite <- x; exact H |
        lra ]
  | H: ?e < 0 |- ?f < 0 =>
      let x := fresh in
      cut (e = f); [
        intro x; try rewrite <- x; exact H |
        lra ]
  | H: ?e = 0 |- ?f = 0 =>
      let x := fresh in
      cut (e = f); [
        intro x; try rewrite <- x; exact H |
        lra ]
  end.


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
