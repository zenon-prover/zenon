(*  Copyright 1997 INRIA  *)
Misc.version "$Id: globals.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

let step_count = ref 0;;
let warnings_flag = ref true;;
let stats_flag = ref false;;
let size_limit = ref infinity;;
let time_limit = ref infinity;;

let progress_flag = ref false;;

let progress f =
  if !progress_flag then begin
    flush stdout;
    flush stderr;
    f ();
    flush stdout;
    flush stderr;
  end;
;;

let inferences = ref 0;;
let proof_nodes = ref 0;;
let top_num_forms = ref 0;;
let stored_lemmas = ref 0;;
let num_expr = ref 0;;

let goal_found = ref false;;
