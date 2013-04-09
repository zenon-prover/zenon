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
  let cc = CC.add cc t in
  OUnit.assert_bool "mem" (CC.mem cc t);
  let t2 = parse "(f (g (h x)))" in
  OUnit.assert_bool "not mem" (not (CC.mem cc t2));
  OUnit.assert_bool "not eq" (not (CT.eq t t2));
  ()

let test_merge () =
  let t1 = parse "((f (a b)) c)" in
  let t2 = parse "((f (a b2)) c2)" in
  let cc = CC.create 5 in
  let cc = CC.add cc t1 in
  let cc = CC.add cc t2 in
  (* merge b and b2 *)
  let cc = CC.assert_eq cc (parse "b") (parse "b2") in
  OUnit.assert_bool "not eq" (not (CC.eq cc t1 t2));
  (* merge c and c2 *)
  let cc = CC.assert_eq cc (parse "c") (parse "c2") in
  OUnit.assert_bool "eq_sub" (CC.eq cc (parse "c") (parse "c2"));
  OUnit.assert_bool "eq" (CC.eq cc t1 t2);
  ()

let suite =
  "test_cc" >:::
    [ "test_add" >:: test_add;
      "test_merge" >:: test_merge;
    ]
