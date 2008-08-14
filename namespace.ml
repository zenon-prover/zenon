(*  Copyright 2006 INRIA  *)
Version.add "$Id: namespace.ml,v 1.3 2008-08-14 14:02:09 doligez Exp $";;

let prefix = "zenon_";;

let anon_prefix = prefix ^ "A";;
let builtin_prefix = prefix ^ "B";;
let hyp_prefix = prefix ^ "H";;
let lemma_prefix = prefix ^ "L";;
let tau_prefix = prefix ^ "T";;
let var_prefix = prefix ^ "V";;
let meta_prefix = prefix ^ "X";;

let goal_name = prefix ^ "G";;
let any_name = prefix ^ "E";;
let univ_name = prefix ^ "U";;

let thm_default_name = prefix ^ "thm";;

let tuple_name = builtin_prefix ^ "tuple";;
