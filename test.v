(* PROOF-FOUND *)
(* BEGIN-CONTEXT *)
Add LoadPath "/usr/local/lib".
Require Import zenon.
Require Import ZArith.
Require Import Omega.
Require Import QArith.
Require Import zenon_arith.
Parameter zenon_U : Set.
Parameter zenon_E : zenon_U.
(* END-CONTEXT *)
(* BEGIN-PROOF *)
Theorem test : (forall X : Z, (forall Y : Z, (((27%Z # 1)%Q > (((11%Z * X%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q)\/(((((11%Z * X%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q > (45%Z # 1)%Q)\/(((-10%Z # 1)%Q > (((7%Z * X%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q)\/((((7%Z * X%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q > (4%Z # 1)%Q)))))).
Proof.
apply NNPP. intro zenon_G.
apply (zenon_notallex_s (fun X : Z => (forall Y : Z, (((27%Z # 1)%Q > (((11%Z * X%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q)\/(((((11%Z * X%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q > (45%Z # 1)%Q)\/(((-10%Z # 1)%Q > (((7%Z * X%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q)\/((((7%Z * X%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q > (4%Z # 1)%Q)))))) zenon_G); [ zenon_intro zenon_H3; idtac ].
elim zenon_H3. zenon_intro zenon_TX_a. zenon_intro zenon_H4.
apply (zenon_notallex_s (fun Y : Z => (((27%Z # 1)%Q > (((11%Z * zenon_TX_a%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q)\/(((((11%Z * zenon_TX_a%Z)%Z + (13%Z * Y%Z)%Z)%Z # 1)%Q > (45%Z # 1)%Q)\/(((-10%Z # 1)%Q > (((7%Z * zenon_TX_a%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q)\/((((7%Z * zenon_TX_a%Z)%Z + (-9%Z * Y%Z)%Z)%Z # 1)%Q > (4%Z # 1)%Q))))) zenon_H4); [ zenon_intro zenon_H5; idtac ].
elim zenon_H5. zenon_intro zenon_TY_b. zenon_intro zenon_H6.
apply (zenon_notor_s _ _ zenon_H6). zenon_intro zenon_H8. zenon_intro zenon_H7.
apply (zenon_notor_s _ _ zenon_H7). zenon_intro zenon_Ha. zenon_intro zenon_H9.
apply (zenon_notor_s _ _ zenon_H9). zenon_intro zenon_Hc. zenon_intro zenon_Hb.
apply (arith_refut _ _ (arith_neg_gt (27%Z # 1)%Q (((11%Z * zenon_TX_a%Z)%Z + (13%Z * zenon_TY_b%Z)%Z)%Z # 1)%Q)); [zenon_intro zenon_Hd | arith_simpl zenon_H8].
pose (zenon_Vf := ((- (11%Z * zenon_TX_a%Z)%Z)%Z - (13%Z * zenon_TY_b%Z)%Z)%Z).
  pose proof (Z.eq_refl zenon_Vf) as zenon_He; change zenon_Vf with ((- (11%Z * zenon_TX_a%Z)%Z)%Z - (13%Z * zenon_TY_b%Z)%Z)%Z in zenon_He at 2.
  cut ((zenon_Vf%Z # 1)%Q <= (-27%Z # 1)%Q); [zenon_intro zenon_Hf | subst zenon_Vf; arith_simpl zenon_Hd ].
apply (arith_refut _ _ (arith_neg_gt (((11%Z * zenon_TX_a%Z)%Z + (13%Z * zenon_TY_b%Z)%Z)%Z # 1)%Q (45%Z # 1)%Q)); [zenon_intro zenon_H10 | arith_simpl zenon_Ha].
pose (zenon_Vg := ((11%Z * zenon_TX_a%Z)%Z + (13%Z * zenon_TY_b%Z)%Z)%Z).
  pose proof (Z.eq_refl zenon_Vg) as zenon_H11; change zenon_Vg with ((11%Z * zenon_TX_a%Z)%Z + (13%Z * zenon_TY_b%Z)%Z)%Z in zenon_H11 at 2.
  cut ((zenon_Vg%Z # 1)%Q <= (45%Z # 1)%Q); [zenon_intro zenon_H12 | subst zenon_Vg; arith_simpl zenon_H10 ].
apply (arith_refut _ _ (arith_neg_gt (-10%Z # 1)%Q (((7%Z * zenon_TX_a%Z)%Z + (-9%Z * zenon_TY_b%Z)%Z)%Z # 1)%Q)); [zenon_intro zenon_H13 | arith_simpl zenon_Hc].
pose (zenon_Vh := ((- (7%Z * zenon_TX_a%Z)%Z)%Z + (9%Z * zenon_TY_b%Z)%Z)%Z).
  pose proof (Z.eq_refl zenon_Vh) as zenon_H14; change zenon_Vh with ((- (7%Z * zenon_TX_a%Z)%Z)%Z + (9%Z * zenon_TY_b%Z)%Z)%Z in zenon_H14 at 2.
  cut ((zenon_Vh%Z # 1)%Q <= (10%Z # 1)%Q); [zenon_intro zenon_H15 | subst zenon_Vh; arith_simpl zenon_H13 ].
apply (arith_refut _ _ (arith_neg_gt (((7%Z * zenon_TX_a%Z)%Z + (-9%Z * zenon_TY_b%Z)%Z)%Z # 1)%Q (4%Z # 1)%Q)); [zenon_intro zenon_H16 | arith_simpl zenon_Hb].
pose (zenon_Vi := ((7%Z * zenon_TX_a%Z)%Z - (9%Z * zenon_TY_b%Z)%Z)%Z).
  pose proof (Z.eq_refl zenon_Vi) as zenon_H17; change zenon_Vi with ((7%Z * zenon_TX_a%Z)%Z - (9%Z * zenon_TY_b%Z)%Z)%Z in zenon_H17 at 2.
  cut ((zenon_Vi%Z # 1)%Q <= (4%Z # 1)%Q); [zenon_intro zenon_H18 | subst zenon_Vi; arith_simpl zenon_H16 ].
destruct (arith_branch zenon_TY_b%Z 1) as [ zenon_H1a | zenon_H19 ]; [ | simpl in zenon_H19 ].
destruct (arith_branch zenon_TX_a%Z 1) as [ zenon_H1c | zenon_H1b ]; [ | simpl in zenon_H1b ].
cut (((((- (13%Z * zenon_TY_b%Z)%Z)%Z - (11%Z * zenon_TX_a%Z)%Z)%Z - zenon_Vf%Z)%Z # 1)%Q == (0%Z # 1)%Q); [ zenon_intro zenon_H1d | subst zenon_Vf; arith_unfold; omega ].
cut ((zenon_Vf%Z # 1)%Q >= (-24%Z # 1)%Q); [ zenon_intro zenon_H1e | arith_unfold_in zenon_H1d; arith_unfold_in zenon_H1a; arith_unfold_in zenon_H1c; arith_unfold; omega ].
pose proof (Qle_trans _ _ _ zenon_H1e zenon_Hf) as Arith_tmp; arith_simpl Arith_tmp.
cut (((((- (9%Z * zenon_TY_b%Z)%Z)%Z + (7%Z * zenon_TX_a%Z)%Z)%Z - zenon_Vi%Z)%Z # 1)%Q == (0%Z # 1)%Q); [ zenon_intro zenon_H1f | subst zenon_Vi; arith_unfold; omega ].
cut ((zenon_Vi%Z # 1)%Q >= (5%Z # 1)%Q); [ zenon_intro zenon_H20 | arith_unfold_in zenon_H1f; arith_unfold_in zenon_H1a; arith_unfold_in zenon_H1b; arith_unfold; omega ].
pose proof (Qle_trans _ _ _ zenon_H20 zenon_H18) as Arith_tmp; arith_simpl Arith_tmp.
destruct (arith_branch zenon_TX_a%Z 1) as [ zenon_H1c | zenon_H1b ]; [ | simpl in zenon_H1b ].
cut (((((9%Z * zenon_TY_b%Z)%Z - (7%Z * zenon_TX_a%Z)%Z)%Z - zenon_Vh%Z)%Z # 1)%Q == (0%Z # 1)%Q); [ zenon_intro zenon_H21 | subst zenon_Vh; arith_unfold; omega ].
cut ((zenon_Vh%Z # 1)%Q >= (11%Z # 1)%Q); [ zenon_intro zenon_H22 | arith_unfold_in zenon_H21; arith_unfold_in zenon_H19; arith_unfold_in zenon_H1c; arith_unfold; omega ].
pose proof (Qle_trans _ _ _ zenon_H22 zenon_H15) as Arith_tmp; arith_simpl Arith_tmp.
cut (((((13%Z * zenon_TY_b%Z)%Z + (11%Z * zenon_TX_a%Z)%Z)%Z - zenon_Vg%Z)%Z # 1)%Q == (0%Z # 1)%Q); [ zenon_intro zenon_H23 | subst zenon_Vg; arith_unfold; omega ].
cut ((zenon_Vg%Z # 1)%Q >= (48%Z # 1)%Q); [ zenon_intro zenon_H24 | arith_unfold_in zenon_H23; arith_unfold_in zenon_H19; arith_unfold_in zenon_H1b; arith_unfold; omega ].
pose proof (Qle_trans _ _ _ zenon_H24 zenon_H12) as Arith_tmp; arith_simpl Arith_tmp.
Qed.
(* END-PROOF *)
