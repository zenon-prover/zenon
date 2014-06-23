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
(* WORK HERE *)
(* pose (zenon_Vf := ((- (11%Z * zenon_TX_a%Z)%Z)%Z - (13%Z * zenon_TY_b%Z)%Z)%Z). *)
pose (x := ((2 # 1))).
pose proof (Qle_refl x).
change x with (2 # 1) in H at 2.
(* WORK HERE *)
set (zenon_Vg := ((11%Z * zenon_TX_a%Z)%Z + (13%Z * zenon_TY_b%Z)%Z)%Z).
(* WORK HERE *)
set (zenon_Vh := ((- (7%Z * zenon_TX_a%Z)%Z)%Z + (9%Z * zenon_TY_b%Z)%Z)%Z).
(* WORK HERE *)
set (zenon_Vi := ((7%Z * zenon_TX_a%Z)%Z - (9%Z * zenon_TY_b%Z)%Z)%Z).
pose proof (Qle_trans _ _ _ zenon_He zenon_Hd) as Arith_tmp; arith_simpl Arith_tmp.
pose proof (Qle_trans _ _ _ zenon_H10 zenon_Hf) as Arith_tmp; arith_simpl Arith_tmp.
pose proof (Qle_trans _ _ _ zenon_H12 zenon_H11) as Arith_tmp; arith_simpl Arith_tmp.
pose proof (Qle_trans _ _ _ zenon_H14 zenon_H13) as Arith_tmp; arith_simpl Arith_tmp.
Qed.
(* END-PROOF *)
