(*  Copyright 2004 INRIA  *)
Version.add "$Id$";;

open Printf;;

open Expr;;
open Phrase;;
open Namespace;;

let report_error lexbuf msg =
  Error.errpos (Lexing.lexeme_start_p lexbuf) msg;
  exit 2;
;;

(* Mapping from TPTP identifiers to coq expressions. *)
let trans_table = Hashtbl.create 35;;

(* Names of formula that have to be treated as (real) definitions. *)
let eq_defs = ref [];;

(* Theorem name according to annotations. *)
let annot_thm_name = ref "";;

(* Theorem name according to TPTP syntax. *)
let tptp_thm_name = ref "";;

(* Names of formulas that should be omitted. *)
let to_ignore = ref [];;

let add_ignore_directive ext fname =
  if ext = "core" || Extension.is_active ext
  then to_ignore := fname :: !to_ignore;
;;

let keep form =
  match form with
    | Hyp (name, _, _) -> not (List.mem name !to_ignore)
    | Rew (name, _, _) -> not (List.mem name !to_ignore)
    | Def _
    | Sig _
    | Inductive _
      -> assert false
;;

let add_annotation s =
  try
    let annot_key = String.sub s 0 (String.index s ' ') in
    match annot_key with
      | "coq_binding" ->
          Scanf.sscanf s "coq_binding %s is %s" (Hashtbl.add trans_table)
      | "eq_def" ->
          Scanf.sscanf s "eq_def %s" (fun x -> eq_defs := x :: !eq_defs)
      | "thm_name" ->
          Scanf.sscanf s "thm_name %s" (fun x -> annot_thm_name := x)
      | "zenon_ignore" ->
          Scanf.sscanf s "zenon_ignore %s %s" add_ignore_directive
      | _ -> ()
  with
    | Scanf.Scan_failure _ -> ()
    | End_of_file -> ()
    | Not_found -> ()
;;

let tptp_to_coq s = try Hashtbl.find trans_table s with Not_found -> s;;

let rec make_annot_expr e =
  match e with
  | Evar _ -> e
  | Emeta _  -> e
  | Eapp (Evar(s,_), l, _) ->
      let s = tptp_to_coq s in
      let l = List.map make_annot_expr l in
      eapp (evar s, l)
  | Eapp(_) -> assert false
  | Enot (e,_) -> enot (make_annot_expr e)
  | Eand (e1,e2,_) -> eand (make_annot_expr e1, make_annot_expr e2)
  | Eor (e1,e2,_) -> eor (make_annot_expr e1, make_annot_expr e2)
  | Eimply (e1,e2,_) -> eimply (make_annot_expr e1, make_annot_expr e2)
  | Eequiv (e1,e2,_) -> eequiv (make_annot_expr e1, make_annot_expr e2)
  | Etrue | Efalse -> e
  | Eall (x,s,e,_) -> eall (x, s, make_annot_expr e)
  | Eex (x,s,e,_) -> eex (x, s, make_annot_expr e)
  | Etau (x,s,e,_) -> etau (x, s, make_annot_expr e)
  | Elam (x,s,e,_) -> elam (x, s, make_annot_expr e)
;;

let make_definition name form body p =
  try Def (Phrase.change_to_def (Extension.predef ()) body)
  with Invalid_argument _ ->
    let msg = sprintf "annotated formula %s is not a definition" name in
    Error.warn msg;
    form
;;

let process_annotations forms =
  let process_one form =
    match form with
      | Hyp (name, body, kind) ->
          if List.mem name !eq_defs then
            make_definition name form (make_annot_expr body) kind
          else
            Hyp (tptp_to_coq name, make_annot_expr body, kind)
      | Rew (name, body, kind) ->
	Rew (tptp_to_coq name, make_annot_expr body, kind)
      | Def _
      | Sig _
      | Inductive _
        -> assert false
  in
  List.rev (List.rev_map process_one (List.filter keep forms))
;;

(* axioms list from B book to transform into rewrite rules.
   names are "hard-coded" / coming from file SimpleBwhy.why
 *)


let axiom_to_rwrt_prop = [
  "infix_eqeq_def";
  "subset_def"; 
  "subsetnoteq_def";
  "empty1";
  "mem_singleton";
  "all_def";
  "mem_union";
  "mem_inter";
  "mem_diff";
  "mem_b_bool";
  "mem_times";
  "mem_power";
  (*"extensionality";*)
  "mem_relation";
  "mem_inverse";
  "mem_dom";
  "mem_ran";
  "mem_semicolon";
  "mem_id";
  "mem_domain_restriction";
  "mem_range_restriction";
  "mem_domain_substraction";
  "mem_range_substraction";
  "mem_image";
  "mem_overriding";
  "mem_direct_product";
  "mem_proj_op_1";
  "mem_proj_op_2";
  "mem_parallel_product";
  "mem_partial_function_set";
  "mem_total_function_set";
  "mem_partial_injection_set";
  "mem_total_injection_set";
  "mem_partial_surjection_set";
  "mem_total_surjection_set";
  "mem_partial_bijection_set";
  "mem_total_bijection_set";
  
  "abs_le";
  "abs_pos";
  "is_empty_def";
  "empty_def1";
  "add_def1";
  "remove_def1";
 (* "mem_natural";
  "mem_natural1";
  "mem_nat";
  "mem_nat1";
  "mem_bounded_int";*)
  "mem_interval";
  "mem_non_empty_power";
  "is_finite_subset";
  "is_finite_subset_def";
  "non_empty_finite_subsets";
(*  "closure_def";
  "closure1_def";*)
  "generalized_union_def";
(*  "seq_def";*)
];;


let axiom_to_rwrt_term = [
  "tuple2_proj_1_def";
  "tuple2_proj_2_def";
  "tuple2_inversion";
  "semicolon_back1";
(*  "power_0";*)
  "power_1";
  "seq_length_def"; 
];;


let is_commut_term body = 
  match body with 
  | Eapp (Evar("b_equal_set", _), [t1; t2], _) -> 
    begin 
      match t1, t2 with 
      | Eapp (Evar(sym1, _), [e11; e12], _), Eapp (Evar(sym2, _), [e21; e22], _) 
	  when 
	    (sym1 = sym2) 
	    && (Expr.equal e11 e22) 
	    && (Expr.equal e12 e21)
	    -> true
      | _ -> false
    end 
  | Eapp (Evar("=", _), [t1; t2], _) -> 
     begin 
      match t1, t2 with 
      | Eapp (Evar(sym1, _), [e11; e12], _), Eapp (Evar(sym2, _), [e21; e22], _) 
	  when 
	    (sym1 = sym2) 
	    && (Expr.equal e11 e22) 
	    && (Expr.equal e12 e21)
	    -> true
      | _ -> false
    end 
  
  | _ -> false
;;

let is_assoc_term body = 
  match body with 
  | Eapp (Evar("b_equal_set", _), [t1; t2], _) -> 
    begin 
      match t1, t2 with 
      | Eapp (Evar(sym11, _), [e11; Eapp (Evar(sym12, _), [e12; e13], _)], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _); e23], _)
	  when 
	    (sym11 = sym12)
	    && (sym12 = sym21)
	    && (sym21 = sym22)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e23)
	    -> true
      | Eapp (Evar(sym11, _), [Eapp (Evar(sym12, _), [e11; e12], _); e13], _),
	Eapp (Evar(sym21, _), [e21; Eapp (Evar(sym22, _), [e22; e23], _)], _)
	  when 
	    (sym11 = sym12)
	    && (sym12 = sym21)
	    && (sym21 = sym22)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e23)
	    -> true
      | _ -> false
    end

  | Eapp (Evar("=", _), [t1; t2], _) -> 
    begin 
      match t1, t2 with 
      | Eapp (Evar(sym11, _), [e11; Eapp (Evar(sym12, _), [e12; e13], _)], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _); e23], _)
	  when 
	    (sym11 = sym12)
	    && (sym12 = sym21)
	    && (sym21 = sym22)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e23)
	    -> true
      | Eapp (Evar(sym11, _), [Eapp (Evar(sym12, _), [e11; e12], _); e13], _),
	Eapp (Evar(sym21, _), [e21; Eapp (Evar(sym22, _), [e22; e23], _)], _)
	  when 
	    (sym11 = sym12)
	    && (sym12 = sym21)
	    && (sym21 = sym22)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e23)
	    -> true
      | _ -> false
    end
  | _ -> false
;;

let is_distrib_term body = 
  match body with 
  | Eapp (Evar("=", _), [t1; t2], _) -> 
    begin 
      match t1, t2 with 
      | Eapp (Evar(sym11, _), [e11; Eapp (Evar(sym12, _), [e12; e13], _)], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _); 
			       Eapp (Evar(sym23, _), [e23; e24], _)], _)
	  when
	    (sym11 = sym22)
	    && (sym22 = sym23)
	    && (sym12 = sym21)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e21 e23)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e24)
	    -> true
      | Eapp (Evar(sym11, _), [Eapp (Evar(sym12, _), [e11; e12], _); e13], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _);
			       Eapp (Evar(sym23, _), [e23; e24], _)], _)
	  when
	    (sym11 = sym22)
	    && (sym22 = sym23)
	    && (sym12 = sym21)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e23)
	    && (Expr.equal e13 e22)
	    && (Expr.equal e22 e24)
	    -> true
      | _ -> false
    end
| Eapp (Evar("=", _), [t1; t2], _) -> 
    begin 
      match t1, t2 with 
      | Eapp (Evar(sym11, _), [e11; Eapp (Evar(sym12, _), [e12; e13], _)], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _); 
			       Eapp (Evar(sym23, _), [e23; e24], _)], _)
	  when
	    (sym11 = sym22)
	    && (sym22 = sym23)
	    && (sym12 = sym21)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e21 e23)
	    && (Expr.equal e12 e22)
	    && (Expr.equal e13 e24)
	    -> true
      | Eapp (Evar(sym11, _), [Eapp (Evar(sym12, _), [e11; e12], _); e13], _),
        Eapp (Evar(sym21, _), [Eapp (Evar(sym22, _), [e21; e22], _);
			       Eapp (Evar(sym23, _), [e23; e24], _)], _)
	  when
	    (sym11 = sym22)
	    && (sym22 = sym23)
	    && (sym12 = sym21)
	    && (Expr.equal e11 e21)
	    && (Expr.equal e12 e23)
	    && (Expr.equal e13 e22)
	    && (Expr.equal e22 e24)
	    -> true
      | _ -> false
    end
  
  | _ -> false
;;

let rec test_fv l1 l2 = 
  match l2 with 
  | [] -> true
  | h :: tl when List.mem h l1 -> test_fv l1 tl
  | _ -> false
;;

let is_literal_noteq body = 
  match body with 
  | Eapp(Evar(sym, _), _, _) when (sym <> "=") -> true
  | Enot(Eapp(Evar(sym, _), _, _), _) when (sym <> "=")-> true
  | _ -> false
;;

let is_literal_eq body = 
  match body with 
  | Eapp(Evar(sym, _), _, _)  -> true
  | Enot(Eapp(Evar(sym, _), _, _), _)  -> true
  | _ -> false
;;

(* let rec is_equal_term body = 
  match body with 
  | Eapp ("=", [t1; t2], _) 
      when not (is_commut_term body)
      -> true
  | _ -> false
;; *)

let rec is_equal_term body = 
  match body with 
  | Eapp (Evar("=", _), [t1; t2], _) 
      when not (is_commut_term body) -> 
     begin 
       match t1, t2 with 
       | Evar (_, _), Evar(_, _) -> false
       | _, Evar (_, _) -> test_fv (get_fv t1) (get_fv t2)
       | Evar (_, _) , _ -> test_fv (get_fv t2) (get_fv t1)
       | _, _ -> true
     end
  | Eapp (Evar("=", _), [t1; t2], _) 
       when not (is_commut_term body) -> 
     begin 
       match t1, t2 with 
       | Evar (_, _), Evar(_, _) -> false
       | _, Evar (_, _) -> test_fv (get_fv t1) (get_fv t2)
       | Evar (_, _) , _ -> test_fv (get_fv t2) (get_fv t1)
       | _, _ -> true
     end
  
  | _ -> false
;;

let rec is_conj_term body = 
  match body with 
  | Eand (e1, e2, _) -> is_conj_term e1 && is_conj_term e2
  | _ -> is_equal_term body
;;

let rec is_rwrt_term body = 
  match body with 
  | Eall (_, _, pred, _) -> is_rwrt_term pred
  | _ -> is_conj_term body
;;

let rec is_equiv_prop body = 
  if is_literal_noteq body 
  then true
  else
    begin
      match body with
      | Eequiv (e1, e2, _) -> 
	 begin 
	   (is_literal_eq e1 
	    && test_fv (get_fv e1) (get_fv e2))
	   || 
	     (is_literal_eq e2 
	      && test_fv (get_fv e2) (get_fv e1))
	 end
      | _ -> false
    end
;;

let rec is_conj_prop body = 
  match body with 
  | Eand (e1, e2, _) -> (is_conj_prop e1 && is_conj_prop e2)
  | _ -> is_equiv_prop body
;;

let rec is_rwrt_prop body = 
  match body with 
  | Eall (_, _, pred, _) -> is_rwrt_prop pred
  | _ -> is_conj_prop body
;;

let rec translate_one_rwrt_B dirs accu p =
  match p with
  | Include (f, None) -> try_incl dirs f accu
  | Include (f, Some _) ->
      (* FIXME change try_incl and incl to implement selective include *)
      (* for the moment, we just ignore the include *)
      accu
  | Annotation s -> add_annotation s; accu
  | Formula (name, "axiom", body) -> 
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 0) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 1) :: accu
       else Hyp (name, body, 2) :: accu
     end
  | Formula (name, "definition", body) ->
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 0) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 1) :: accu
       else Hyp (name, body, 2) :: accu
     end
  | Formula (name, "hypothesis", body) ->
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 0) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 1) :: accu
       else Hyp (name, body, 1) :: accu
     end
  | Formula (name, ("lemma"|"theorem"), body) ->
      Hyp (name, body, 1) :: accu
  | Formula (name, "conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 0) :: accu
  | Formula (name, "negated_conjecture", body) ->
      Hyp (name, body, 0) :: accu
(* TFF formulas *)
  | Formula (name, "tff_type", body) ->
     Hyp (name, body, 13) :: accu
  | Formula (name, "tff_axiom", body) -> 
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 10) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 11) :: accu
       else Hyp (name, body, 12) :: accu
     end
  | Formula (name, "tff_definition", body) ->
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 10) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 11) :: accu
       else Hyp (name, body, 12) :: accu
     end
  | Formula (name, "tff_hypothesis", body) ->
     begin
       if List.mem name axiom_to_rwrt_term
       then Rew (name, body, 10) :: accu
       else if List.mem name axiom_to_rwrt_prop
       then Rew (name, body, 11) :: accu
       else Hyp (name, body, 11) :: accu
     end
(*  | Formula (name, ("tff_axiom" | "tff_definition"), body) ->
      Hyp (name, body, 12) :: accu
  | Formula (name, "tff_hypothesis", body) ->
      Hyp (name, body, 11) :: accu
 *)  | Formula (name, ("tff_lemma"|"tff_theorem"), body) ->
      Hyp (name, body, 11) :: accu
  | Formula (name, "tff_conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 10) :: accu
  | Formula (name, "tff_negated_conjecture", body) ->
      Hyp (name, body, 10) :: accu
  | Formula (name, k, body) ->
      Error.warn ("unknown formula kind: " ^ k);
      Hyp (name, body, 1) :: accu

and translate_one_rwrt dirs accu p =
  match p with
  | Include (f, None) -> try_incl dirs f accu
  | Include (f, Some _) ->
      (* FIXME change try_incl and incl to implement selective include *)
      (* for the moment, we just ignore the include *)
      accu
  | Annotation s -> add_annotation s; accu
  | Formula (name, "axiom" , body) ->
    begin 
      if is_rwrt_term body
      then Rew (name, body, 0) :: accu
      else if is_rwrt_prop body 
      then Rew (name, body, 1) :: accu
      else Hyp (name, body, 2) :: accu
    end
  | Formula (name, "definition", body) ->
    begin 
      if is_rwrt_term body
      then Rew (name, body, 0) :: accu
      else if is_rwrt_prop body 
      then Rew (name, body, 1) :: accu
      else Hyp (name, body, 2) :: accu
    end
  | Formula (name, "hypothesis", body) ->
    begin 
      if is_rwrt_term body
      then Rew (name, body, 0) :: accu
      else if is_rwrt_prop body 
      then Rew (name, body, 1) :: accu
      else Hyp (name, body, 1) :: accu
    end
  | Formula (name, ("lemma"|"theorem"), body) ->
      Hyp (name, body, 1) :: accu
  | Formula (name, "conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 0) :: accu
  | Formula (name, "negated_conjecture", body) ->
      Hyp (name, body, 0) :: accu
(* TFF formulas *)
  | Formula (name, "tff_type", body) ->
      Hyp (name, body, 13) :: accu
  | Formula (name, ("tff_axiom" | "tff_definition"), body) ->
      Hyp (name, body, 12) :: accu
  | Formula (name, "tff_hypothesis", body) ->
      Hyp (name, body, 11) :: accu
  | Formula (name, ("tff_lemma"|"tff_theorem"), body) ->
      Hyp (name, body, 11) :: accu
  | Formula (name, "tff_conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 10) :: accu
  | Formula (name, "tff_negated_conjecture", body) ->
      Hyp (name, body, 10) :: accu
  | Formula (name, k, body) ->
      Error.warn ("unknown formula kind: " ^ k);
      Hyp (name, body, 1) :: accu

and translate_one dirs accu p =
  match p with
  | Include (f, None) -> try_incl dirs f accu
  | Include (f, Some _) ->
      (* FIXME change try_incl and incl to implement selective include *)
      (* for the moment, we just ignore the include *)
      accu
  | Annotation s -> add_annotation s; accu
  | Formula (name, "axiom", body) -> 
    Hyp (name, body, 2) :: accu
  | Formula (name, "rwrt_term", body) -> 
    Rew (name, body, 0) :: accu
  | Formula (name, "rwrt_prop", body) -> 
    Rew (name, body, 1) :: accu
  | Formula (name, "definition", body) ->
      Hyp (name, body, 2) :: accu
  | Formula (name, "hypothesis", body) ->
    Hyp (name, body, 1) :: accu
  | Formula (name, ("lemma"|"theorem"), body) ->
      Hyp (name, body, 1) :: accu
  | Formula (name, "conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 0) :: accu
  | Formula (name, "negated_conjecture", body) ->
      Hyp (name, body, 0) :: accu
  (* TFF formulas *)
  | Formula (name, "tff_type", body) ->
      Hyp (name, body, 13) :: accu
  | Formula (name, ("tff_axiom" | "tff_definition"), body) ->
      Hyp (name, body, 12) :: accu
  | Formula (name, "tff_hypothesis", body) ->
      Hyp (name, body, 11) :: accu
  | Formula (name, ("tff_lemma"|"tff_theorem"), body) ->
      Hyp (name, body, 11) :: accu
  | Formula (name, "tff_conjecture", body) ->
      tptp_thm_name := name;
      Hyp (goal_name, enot (body), 10) :: accu
  | Formula (name, "tff_negated_conjecture", body) ->
      Hyp (name, body, 10) :: accu
  (* Fallback *)
  | Formula (name, k, body) ->
      Error.warn ("unknown formula kind: " ^ k);
      Hyp (name, body, 1) :: accu

and xtranslate dirs ps accu =
  if !Globals.build_rwrt_sys_B
  then List.fold_left (translate_one_rwrt_B dirs) accu ps
  else if !Globals.build_rwrt_sys 
  then List.fold_left (translate_one_rwrt dirs) accu ps
  else List.fold_left (translate_one dirs) accu ps

and try_incl dirs f accu =
  let rec loop = function
    | [] ->
        let msg = sprintf "file %s not found in include path" f in
        Error.err msg;
        raise Error.Abort;
    | h::t -> begin
        try incl dirs (Filename.concat h f) accu
        with Sys_error _ -> loop t
      end
  in
  loop dirs

and incl dir name accu =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  lexbuf.Lexing.lex_curr_p <- {
    Lexing.pos_fname = name;
    Lexing.pos_lnum = 1;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0;
  };
  try
    let tpphrases = Parsetptp.file Lextptp.token lexbuf in
    close_in chan;
    xtranslate dir tpphrases accu;
  with
  | Parsing.Parse_error -> report_error lexbuf "syntax error."
  | Error.Lex_error msg -> report_error lexbuf msg
;;

let translate dirs ps =
  let raw = List.rev (xtranslate dirs ps []) in
  let cooked = process_annotations raw in
  let name = if !annot_thm_name <> "" then !annot_thm_name
             else if !tptp_thm_name <> "" then !tptp_thm_name
             else thm_default_name
  in
  (cooked, name)
;;
