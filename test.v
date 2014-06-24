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
Theorem associative_sum_exists : (exists X : Z, (exists Y : Z, (exists Z' : Z, (exists Z1 : Z, (exists Z2 : Z, (exists Z3 : Z, (exists Z4 : Z, (((((X%Z + Y%Z)%Z # 1)%Q == (Z1%Z # 1)%Q)/\((((Z1%Z + Z'%Z)%Z # 1)%Q == (Z2%Z # 1)%Q)/\((((Y%Z + Z'%Z)%Z # 1)%Q == (Z3%Z # 1)%Q)/\(((X%Z + Z3%Z)%Z # 1)%Q == (Z4%Z # 1)%Q))))->((Z2%Z # 1)%Q == (Z4%Z # 1)%Q))))))))).
Proof.
apply NNPP. intro zenon_G.
apply zenon_G. exists Z0. apply NNPP. zenon_intro zenon_H8.
apply zenon_H8. exists Z0. apply NNPP. zenon_intro zenon_H9.
apply zenon_H9. exists Z0. apply NNPP. zenon_intro zenon_Ha.
apply zenon_Ha. exists Z0. apply NNPP. zenon_intro zenon_Hb.
apply zenon_Hb. exists Z0. apply NNPP. zenon_intro zenon_Hc.
apply zenon_Hc. exists Z0. apply NNPP. zenon_intro zenon_Hd.
apply zenon_Hd. exists Z0. apply NNPP. zenon_intro zenon_He.
apply (zenon_notimply_s _ _ zenon_He). zenon_intro zenon_H10. zenon_intro zenon_Hf.
apply zenon_H11. apply refl_equal.
Qed.
(* END-PROOF *)
