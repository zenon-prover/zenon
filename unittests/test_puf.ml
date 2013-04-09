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
  let uf = merge_list uf [10;11;12;13;2] in
  (* equiv classes *)
  let l1 = ref [] in
  P.iter_equiv_class uf 1 (fun x -> l1 := x:: !l1);
  let l2 = ref [] in
  P.iter_equiv_class uf 5 (fun x -> l2 := x:: !l2);
  OUnit.assert_equal [1;2;3;10;11;12;13] (List.sort compare !l1);
  OUnit.assert_equal [5;6] (List.sort compare !l2);
  ()

let test_distinct () =
  let uf = P.create 5 in
  let uf = merge_list uf [1;2;3] in
  let uf = merge_list uf [5;6] in
  let uf = P.distinct uf 1 5 in
  OUnit.assert_equal None (P.inconsistent uf);
  let uf' = P.union uf 2 6 in
  OUnit.assert_bool "inconsistent"
    (match P.inconsistent uf' with | None -> false | Some _ -> true);
  OUnit.assert_equal None (P.inconsistent uf);
  let uf = P.union uf 1 10 in
  OUnit.assert_equal None (P.inconsistent uf);
  ()

let suite =
  "test_puf" >:::
    [ "test_union" >:: test_union;
      "test_iter" >:: test_iter;
      "test_distinct" >:: test_distinct;
    ]
