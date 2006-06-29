(*  Copyright 2006 INRIA  *)
(*  $Id: namespace.mli,v 1.2 2006-06-29 08:32:15 doligez Exp $  *)

val anon_prefix : string;;    (* anonymous hypotheses *)
val builtin_prefix : string;; (* built-in symbols *)
val hyp_prefix : string;;     (* local hypotheses *)
val lemma_prefix : string;;   (* lemmas *)
val tau_prefix : string;;     (* skolem constants *)
val var_prefix : string;;     (* gensym variables *)
val meta_prefix : string;;    (* meta variables *)

val goal_name : string;;      (* the goal *)
val any_name : string;;       (* an element of the universe *)
val univ_name : string;;      (* the 1st-order universe *)

val tuple_name : string;;  (* built-in constructor for tuples *)
