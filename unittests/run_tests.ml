open OUnit

let suite =
  "all_tests" >:::
    [ Test_puf.suite;
      Test_cc.suite;
    ]

let _ =
  run_test_tt_main suite

