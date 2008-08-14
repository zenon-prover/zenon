(*  Copyright 1997 INRIA  *)
Version.add "$Id: globals.ml,v 1.20 2008-08-14 14:08:25 pessaux Exp $";;

let debug_flag = ref false;;

let stats_flag = ref false;;
let quiet_flag = ref false;;
let size_limit = ref 100_000_000.;;
let step_limit = ref 10_000.;;
let time_limit = ref 300.;;
let short_flag = ref false;;
let ctx_flag = ref false;;
let random_flag = ref false;;
let random_seed = ref 0;;
let load_path = ref Config.libdir;;
let namespace_flag = ref false;;
let used_for_focalize_flag = ref false ;;

let inferences = ref 0;;
let proof_nodes = ref 0;;
let top_num_forms = ref 0;;
let stored_lemmas = ref 0;;
let num_expr = ref 0;;
