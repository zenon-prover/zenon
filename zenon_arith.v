
Require Import Omega.
Require Export ZArith.
Require Export ZArith.BinInt.
Require Export QArith.
Require Export QArith.Qround.

Ltac arith_unfold :=
  unfold Qplus, Qminus, Qmult, Qeq, Qle, Qlt, Zdiv;
  try repeat rewrite Qmult_1_l;
  try repeat rewrite Qmult_1_r;
  simpl;
  try repeat rewrite Z.mul_1_l;
  try repeat rewrite Z.mul_1_r.

Ltac arith_unfold_in H :=
  unfold Qplus, Qminus, Qmult, Qeq, Qle, Qlt, Zdiv in H;
  try repeat rewrite Qmult_1_l in H;
  try repeat rewrite Qmult_1_r in H;
  simpl in H;
  try repeat rewrite Z.mul_1_l in H;
  try repeat rewrite Z.mul_1_r in H.

Ltac arith_simpl H := arith_unfold; arith_unfold_in H; omega.

Lemma arith_refut : forall P Q: Prop, (P -> Q) -> (Q -> False) -> (P -> False).
Proof. intro P. intro Q. intro Hyp. intro notQ. intro p. exact (notQ (Hyp p)). Qed.

Lemma arith_eq : forall a b: Q, a == b -> a <= b /\ a >= b.
Proof.
arith_unfold. intros. omega.
Qed.

Lemma arith_neq : forall a b: Q, (~ a == b) -> a < b \/ a > b.
Proof.
arith_unfold. intros. omega.
Qed.

Lemma floor_1 : forall a: Z, Qfloor (a # 1) = a.
Proof. intros. unfold Qfloor. apply Zdiv_1_r. Qed.

Lemma arith_tight_leq : forall a: Z, forall b:Q, a # 1 <= b -> a # 1 <= (Qfloor b) # 1.
Proof.
intros. unfold Qle. simpl. rewrite Z.mul_1_r. rewrite Z.mul_1_r.
rewrite <- (floor_1 a). apply Qfloor_resp_le. trivial.
Qed.

Lemma ceiling_1 : forall a: Z, Qceiling (a # 1) = a.
Proof. intros. unfold Qceiling, Qfloor. simpl. rewrite Zdiv_1_r. rewrite Z.opp_involutive. trivial. Qed.

Lemma arith_tight_geq : forall a: Z, forall b:Q, a # 1 >= b -> a # 1 >= (Qceiling b) # 1.
Proof.
intros. unfold Qle. simpl. rewrite Z.mul_1_r. rewrite Z.mul_1_r.
rewrite <- (ceiling_1 a). apply Qceiling_resp_le. trivial.
Qed.
