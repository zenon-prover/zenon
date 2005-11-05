(*  Copyright 1997 INRIA  *)
Version.add "$Id: globals.ml,v 1.14 2005-11-05 11:13:17 doligez Exp $";;

let debug_flag = ref false;;

let warnings_flag = ref true;;
let stats_flag = ref false;;
let quiet_flag = ref false;;
let size_limit = ref 100_000_000.;;
let time_limit = ref 300.;;
let short_flag = ref false;;
let ctx_flag = ref false;;

let inferences = ref 0;;
let proof_nodes = ref 0;;
let top_num_forms = ref 0;;
let stored_lemmas = ref 0;;
let num_expr = ref 0;;
