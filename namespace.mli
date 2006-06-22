(*  Copyright 2006 INRIA  *)
(*  $Id: namespace.mli,v 1.1 2006-06-22 17:09:40 doligez Exp $  *)

val goal_name : string;;     (* the goal *)
val any_name : string;;      (* an element of the universe *)
val univ_name : string;;     (* the 1st-order universe *)

val anon_prefix : string;;   (* anonymous hypotheses *)
val hyp_prefix : string;;    (* local hypotheses *)
val lemma_prefix : string;;  (* lemmas *)
val tau_prefix : string;;    (* skolem constants *)
val var_prefix : string;;    (* gensym variables *)
val meta_prefix : string;;   (* meta variables *)

