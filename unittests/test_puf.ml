(** Tests for persistent union find *)

open OUnit

module P = Puf.Make(struct type t = int let get_id i = i end)

let rec merge_list uf l = match l with
  | [] | [_] -> uf
  | x::((y::_) as l') ->
    merge_list (P.union uf x y) l'

let test_union () =
  let uf = P.create 5 in
  let uf = merge_list uf [1;2;3] in
  let uf = merge_list uf [5;6] in
  OUnit.assert_equal (P.find uf 1) (P.find uf 2);
  OUnit.assert_equal (P.find uf 1) (P.find uf 3);
  OUnit.assert_equal (P.find uf 5) (P.find uf 6);
  OUnit.assert_bool "noteq" ((P.find uf 1) <> (P.find uf 5));
  OUnit.assert_equal 10 (P.find uf 10);
  let uf = P.union uf 1 5 in
  OUnit.assert_equal (P.find uf 2) (P.find uf 6);
  ()

let test_iter () =
  let uf = P.create 5 in
  let uf = merge_list uf [1;2;3] in
  let uf = merge_list uf [5;6] in
  () (* TODO *)

let test_distinct () =
  () (* TODO *)

let suite =
  "test_puf" >:::
    [ "test_union" >:: test_union;
      "test_iter" >:: test_iter;
      "test_distinct" >:: test_distinct;
    ]
