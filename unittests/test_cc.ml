(** Tests for congruence closure *)

open OUnit

let test_add () =
  ()  (* TODO *)

let test_merge () =
  () (* TODO *)

let suite =
  "test_cc" >:::
    [ "test_add" >:: test_add;
      "test_merge" >:: test_merge;
    ]
