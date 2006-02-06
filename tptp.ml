(*  Copyright 2004 INRIA  *)
Version.add "$Id: tptp.ml,v 1.13 2006-02-06 17:56:06 doligez Exp $";;

open Printf;;

open Expr;;
open Phrase;;

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
  if Extension.is_active ext then
    to_ignore := fname :: !to_ignore

let keep form =
  match form with
    | Hyp(name, _, _) -> not (List.mem name !to_ignore)
    | Def def -> assert false
    | Sig _ -> assert false
    | Inductive _ -> assert false
;;

let add_annotation s =
  try
    let annot_kind = String.sub s 0 (String.index s ' ') in
    match annot_kind with
      | "coq_binding" ->
          Scanf.sscanf s "coq_binding %s is %s" (Hashtbl.add trans_table)
      | "eq_def" ->
          Scanf.sscanf s "eq_def %s" (fun x -> eq_defs:= x :: !eq_defs)
      | "thm_name" ->
          Scanf.sscanf s "thm_name %s" (fun x -> thm_name:=x)
      | "zenon_ignore" ->
          Scanf.sscanf s "thm_name %s %s" add_ignore_directive
      | _ -> () (* other annotations are irrelevant for zenon. *)
  with (* unknown annotations. *)
    | Scanf.Scan_failure _ -> ()
    | End_of_file -> ()
    | Not_found -> ()

let tptp_to_coq s = try Hashtbl.find trans_table s with Not_found -> s

let rec make_annot_expr e =
  match e with
  | Evar _ -> e
  | Emeta _  -> e
  | Eapp (s, l, _) ->
      let s = tptp_to_coq s in
      let l = List.map make_annot_expr l in
      eapp (s, l)
  | Enot (e,_) -> enot (make_annot_expr e)
  | Eand (e1,e2,_) -> eand (make_annot_expr e1, make_annot_expr e2)
  | Eor (e1,e2,_) -> eor (make_annot_expr e1, make_annot_expr e2)
  | Eimply (e1,e2,_) -> eimply (make_annot_expr e1, make_annot_expr e2)
  | Eequiv (e1,e2,_) -> eequiv (make_annot_expr e1, make_annot_expr e2)
  | Etrue | Efalse -> e
  | Eall (x,s,e,o,_) -> eall (x, s, make_annot_expr e, o)
  | Eex (x,s,e,o,_) -> eex (x, s, make_annot_expr e, o)
  | Etau (x,s,e,_) -> etau (x, s, make_annot_expr e)
  | Elam (x,s,e,_) -> elam (x, s, make_annot_expr e)
;;

(* transform a fof into a real definition. *)
let make_definition name form body p =
  if Phrase.is_def [] body then begin
    let def = Phrase.make_def (body, p) [] body in
      match def with
        | DefPseudo (_,s,args,def) -> Def (DefReal(s,args,def))
        | DefReal _ -> Def def
  end else begin
    let msg = sprintf "annotated formula %s is not a definition" name in
    Error.warn msg;
    form
  end
;;

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
      | Sig _ -> assert false
      | Inductive _ -> assert false
  in
  List.map process_one (List.filter keep forms)

let rec translate dirs ps =
  match ps with
  | [] -> []
  | Include f :: t -> (try_incl dirs f) @ (translate dirs t)
  | Annotation s :: t -> add_annotation s; translate dirs t
  | Formula (name, "axiom", body) :: t ->
      Hyp (name, body, 2) :: (translate dirs t)
  | Formula (name, "hypothesis", body) :: t ->
      Hyp (name, body, 1) :: (translate dirs t)
  | Formula (name, "conjecture", body) :: t ->
      Hyp ("z'g", enot (body), 0) :: (translate dirs t)
  | Formula (name, "negated_conjecture", body) :: t ->
      Hyp ("z'g", body, 0) :: (translate dirs t)
  | Formula (name, k, body) :: t ->
      Error.warn ("unknown formula kind: " ^ k);
      Hyp (name, body, 1) :: (translate dirs t)

and try_incl dirs f =
  let rec loop = function
    | [] ->
        let msg = sprintf "file %s not found in include path" f in
        Error.err msg;
        raise Error.Abort;
    | h::t -> begin
        try incl dirs (Filename.concat h f)
        with Sys_error _ -> loop t
      end
  in
  loop dirs

and incl dir name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let tpphrases = Parsetptp.file Lextptp.token lexbuf in
  close_in chan;
  translate dir tpphrases
;;
