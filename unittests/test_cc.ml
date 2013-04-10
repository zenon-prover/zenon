(** Tests for congruence closure *)

open OUnit

let parse = CC.parse
let pp = CC.pp

module CT = CC.StrTerm
module CC = CC.StrCC

let test_add () =
  let cc = CC.create 5 in
  let t = parse "((a (b c)) d)" in
  OUnit.assert_equal ~cmp:CT.eq t t;
  let t2 = parse "(f (g (h x)))" in
  OUnit.assert_bool "not eq" (not (CC.eq cc t t2));
  ()

let test_merge () =
  let t1 = parse "((f (a b)) c)" in
  let t2 = parse "((f (a b2)) c2)" in
  (* Format.printf "t1=%a, t2=%a@." pp t1 pp t2; *)
  let cc = CC.create 5 in
  (* merge b and b2 *)
  let cc = CC.merge cc (parse "b") (parse "b2") in
  OUnit.assert_bool "not eq" (not (CC.eq cc t1 t2));
  OUnit.assert_bool "eq_sub" (CC.eq cc (parse "b") (parse "b2"));
  (* merge c and c2 *)
  let cc = CC.merge cc (parse "c") (parse "c2") in
  OUnit.assert_bool "eq_sub" (CC.eq cc (parse "c") (parse "c2"));
  (* Format.printf "t1=%a, t2=%a@." pp (CC.normalize cc t1) pp (CC.normalize cc t2); *)
  OUnit.assert_bool "eq" (CC.eq cc t1 t2);
  ()

let test_merge2 () =
  let cc = CC.create 5 in
  let cc = CC.distinct cc (parse "a") (parse "b") in
  let cc = CC.merge cc (parse "(f c)") (parse "a") in
  let cc = CC.merge cc (parse "(f d)") (parse "b") in
  OUnit.assert_bool "not_eq" (not (CC.can_eq cc (parse "a") (parse "b")));
  OUnit.assert_bool "inconsistent"
    (try ignore (CC.merge cc (parse "c") (parse "d")); false
     with CC.Inconsistent _ -> true);
  ()

let suite =
  "test_cc" >:::
    [ "test_add" >:: test_add;
      "test_merge" >:: test_merge;
      "test_merge2" >:: test_merge2;
    ]
