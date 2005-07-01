(*  Copyright 2004 INRIA  *)
Version.add "$Id: tptp.ml,v 1.8 2005-07-01 12:24:47 prevosto Exp $";;

open Expr;;
open Phrase;;

(* FIXME a faire: enlever le cas particulier pour l'egalite (?) *)

(* translation from TPTP identifier to coq expressions, following annotations
   produced by focal. *)
let trans_table = Hashtbl.create 35;;

(* names of formula that have to be treated as (real) definitions. *)
let eq_defs = ref []

(* name of the coq theorem. *)
let thm_name = ref "theorem"
let get_thm_name () = !thm_name

let to_ignore = ref []

let add_ignore_directive ext fname =
  if Extension.is_enabled ext then
    to_ignore:= fname :: !to_ignore

let keep form = 
  match form with 
      Hyp(name, _, _) -> not (List.mem name !to_ignore)
    | Def def -> assert false

let add_annotation s =
  try
    let annot_kind = String.sub s 0 (String.index s ' ') in
      match annot_kind with
          "coq_binding" ->  
            Scanf.sscanf s "coq_binding %s is %s" (Hashtbl.add trans_table)
        | "eq_def" ->
            Scanf.sscanf s "eq_def %s" (fun x -> eq_defs:= x :: !eq_defs)
        | "thm_name" -> 
            Scanf.sscanf s "thm_name %s" (fun x -> thm_name:=x)
        | "zenon_ignore" ->
            Scanf.sscanf s "thm_name %s %s" add_ignore_directive
        | _ -> () (* other annotations are irrelevant for zenon. *)
  with (* unknown annotations. *)
      Scanf.Scan_failure _ -> ()
    | End_of_file -> ()
    | Not_found -> ()

let tptp_to_coq s = try Hashtbl.find trans_table s with Not_found -> s

let rec make_annot_expr =
  function
      Evar (s,_) -> evar s
    | Emeta (e,_)  -> emeta (make_annot_expr e)
    | Eapp (s, l, _) -> let s = tptp_to_coq s in 
      let l = List.map make_annot_expr l in eapp (s, l)
    | Enot (e,_) -> enot (make_annot_expr e)
    | Eand (e1,e2,_) -> eand (make_annot_expr e1, make_annot_expr e2)
    | Eor (e1,e2,_) -> eor (make_annot_expr e1, make_annot_expr e2)
    | Eimply (e1,e2,_) -> eimply (make_annot_expr e1, make_annot_expr e2)
    | Eequiv (e1,e2,_) -> eequiv (make_annot_expr e1, make_annot_expr e2)
    | Etrue -> etrue | Efalse -> efalse
    | Eall (x,s,e,_) -> eall (x, s, make_annot_expr e)
    | Eex (x,s,e,_) -> eex (x, s, make_annot_expr e)
    | Etau (x,s,e,_) -> etau (x, s, make_annot_expr e)

(* transform a fof into a real definition. *)
let make_definition name form body p =
  if Phrase.is_def [] body then
    let def = Phrase.make_def (body,p)  [] body in
      match def with
          DefPseudo (_,s,args,def) -> Def (DefReal(s,args,def))
        | DefReal _ -> Def def
  else
    (if !Globals.warnings_flag then
       Printf.eprintf "Warning: formula %s is not a definition, \
                       although annotated as one." name;
     form)

let process_annotations forms = 
  let process_one form =
    match form with
      | Hyp (name, body, kind) ->
          if List.mem name !eq_defs then
            make_definition name form (make_annot_expr body) kind
          else
            Hyp (tptp_to_coq name, make_annot_expr body, kind)
      | Def def -> assert false 
          (* for now, TPTP does not directly support definitions. *)
  in
    List.map process_one 
      (List.filter keep forms)

let x = evar "x" and y = evar "y" and z = evar "z";;

let equality_axioms = [
  eall (x, "", eapp ("=", [x; x]));
  eall (x, "",
    eall (y, "", eimply (eapp ("=", [x; y]), eapp ("=", [y; x]))));
  eall (x, "",
    eall (y, "",
      eall (z, "",
        eimply (eand (eapp ("=", [x; y]),
                      eapp ("=", [y; z])),
                eapp ("=", [x; z])))));
];;

let check_arg context v1 v2 a1 a2 =
  match a1, a2 with
  | Evar (w1, _), Evar (w2, _) ->
      a1 == a2 && List.mem a1 context
      || a1 == v1 && a2 == v2
      || a1 == v2 && a2 == v1
  | _, _ -> false
;;

let rec equ_form context f =
  match f with
  | Eall (v, t, g, _) -> equ_form (v::context) g
  | Eimply (Eapp ("=", [(Evar _ as v1); (Evar _ as v2)], _),
            Eapp ("=", [Eapp (s1, l1, _); Eapp (s2, l2, _)], _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | Eimply (Eand (Eapp ("=", [(Evar _ as v1); (Evar _ as v2)], _),
                  Eapp (s1, l1, _), _),
            Eapp (s2, l2, _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | _ -> false
;;

let is_eq_formula f =
  List.exists (Expr.equal f) equality_axioms
  || equ_form [] f
;;

let rec translate dirs ps =
  match ps with
    | [] -> []
    | Include f :: t -> (try_incl dirs f) @ (translate dirs t)
    | Annotation s :: t -> add_annotation s; translate dirs t
    | Formula (name, "axiom", body) :: t ->
        if is_eq_formula body
        then translate dirs t
        else Hyp (name, body, 2) :: (translate dirs t)
    | Formula (name, "hypothesis", body) :: t ->
        if is_eq_formula body
        then translate dirs t
        else Hyp (name, body, 1) :: (translate dirs t)
    | Formula (name, "conjecture", body) :: t ->
        Hyp ("_Zgoal", enot (body), 0) :: (translate dirs t)
    | Formula (name, k, body) :: t ->
        failwith ("unknown formula kind: " ^ k)

and try_incl dirs f =
  let rec loop = function
    | [] -> failwith (Printf.sprintf "file %s not found in include path" f)
    | h::t -> begin
        try incl dirs (Filename.concat h f)
        with Sys_error _ -> loop t
      end
  in
  loop dirs

and incl dir name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let tpphrases = Parser.tpfile Lexer.tptoken lexbuf in
    close_in chan;
    translate dir tpphrases
;;
