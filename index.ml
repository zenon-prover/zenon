(*  Copyright 2004 INRIA  *)
Misc.version "$Id: index.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

open Expr;;
open Mlproof;;
open Printf;;

let tblsize = 997;;  (* reduce to 17 for debugging *)

module HE = Hashtbl.Make (Expr);;

let allforms = (HE.create tblsize : Prio.t HE.t);;

type formula_rec = {
  mutable present : bool;
  mutable proofs : (Mlproof.proof * formula_rec list) list;
};;
let proofs = (HE.create tblsize : formula_rec HE.t);;
let new_forms = ref [];;

let posforms = (Hashtbl.create tblsize : (string, expr list ref) Hashtbl.t);;
let negforms = (Hashtbl.create tblsize : (string, expr list ref) Hashtbl.t);;
let equalforms = (Hashtbl.create tblsize : (string, expr list ref) Hashtbl.t);;
let rewrites = (Hashtbl.create tblsize
                : (string, (expr * expr) list ref) Hashtbl.t);;
let noteqforms = (Hashtbl.create tblsize : (string, expr list ref) Hashtbl.t);;

let act_head action tbl key v =
  match key with
  | Eapp (s, _, _) | Evar (s, _) -> action tbl s v
  | _ -> ()
;;

let act action action2 e =
  match e with
  | Eapp ("=", [(Emeta _ as t1); t2], _) ->
      act_head action equalforms t2 e;
      act_head action2 rewrites t2 (t2, t1);
  | Eapp ("=", [t1; (Emeta _ as t2)], _) ->
      act_head action equalforms t1 e;
      act_head action2 rewrites t1 (t1, t2);
  | Eapp ("=", [t1; t2], _) ->
      act_head action equalforms t1 e;
      act_head action equalforms t2 e;
  | Enot (Eapp ("=", [Emeta _; _], _), _) -> ()
  | Enot (Eapp ("=", [_; Emeta _], _), _) -> ()
  | Enot (Eapp ("=", [t1; t2], _), _) ->
      act_head action noteqforms t1 e;
      act_head action noteqforms t2 e;
  | Enot (f, _) ->
      act_head action negforms f e;
  | f ->
      act_head action posforms f e;
;;

let add_action tbl k v =
  try
    let lr = Hashtbl.find tbl k in
    lr := v :: !lr
  with Not_found ->
    Hashtbl.add tbl k (ref [v]);
;;

let cur_num_forms = ref 0;;

let add e prio =
  HE.add allforms e prio;
  incr cur_num_forms;
  if !cur_num_forms > !Globals.top_num_forms
  then Globals.top_num_forms := !cur_num_forms;
  act add_action add_action e;
  begin try (HE.find proofs e).present <- true with Not_found -> (); end;
  new_forms := e :: !new_forms;
;;

let remove_action tbl k v =
  try
    let lr = Hashtbl.find tbl k in
    match !lr with
    | [] -> assert false
    | [h] -> Hashtbl.remove tbl k;
    | h::t -> lr := t;
  with Not_found -> assert false
;;

let remove e =
  decr cur_num_forms;
  HE.remove allforms e;
  act remove_action remove_action e;
  begin try (HE.find proofs e).present <- false with Not_found -> (); end;
;;

let member e = HE.mem allforms e;;

let get_prio e = HE.find allforms e;;

let find_pos s =
  try !(Hashtbl.find posforms s)
  with Not_found -> []
;;

let find_neg s =
  try !(Hashtbl.find negforms s)
  with Not_found -> []
;;

let find_equal t =   (* t is one member of the equation *)
  match t with
  | Eapp (s, _, _) | Evar (s, _) ->
      begin try !(Hashtbl.find equalforms s)
      with Not_found -> []
      end
  | _ -> []
;;

let find_rewrite t =
  match t with
  | Eapp (s, _, _) | Evar (s, _) ->
      begin try !(Hashtbl.find rewrites s)
      with Not_found -> []
      end
  | _ -> []
;;

let find_noteq t =
  match t with
  | Eapp (s, _, _) | Evar (s, _) ->
      begin try !(Hashtbl.find noteqforms s)
      with Not_found -> []
      end
  | _ -> []
;;

(* ==== *)

let suspects = ref [];;

let add_proof p =
  incr Globals.stored_lemmas;
  let get_record f =
    begin try HE.find proofs f
    with Not_found ->
      let r = {present = HE.mem allforms f; proofs = []} in
      HE.add proofs f r;
      r
    end
  in
  let recs = List.map get_record p.mlconc in
  suspects := [(p, recs)] :: !suspects;
;;

let search_proof () =
  let do_form f =
    try
      let r = HE.find proofs f in
      if r.present then begin
        suspects := r.proofs :: !suspects;
        r.proofs <- [];
      end;
    with Not_found -> ()
  in
  let fs = !new_forms in
  new_forms := [];
  List.iter do_form fs;
  let rec loop () =
    match !suspects with
    | [] -> None
    | [] :: t2 -> suspects := t2; loop ()
    | ((p, recs) as lem :: t1) :: t2 ->
        begin try
          let r = List.find (fun x -> not x.present) recs in
          suspects := t1 :: t2;
          r.proofs <- lem :: r.proofs;
          loop ()
        with Not_found ->
          Some p
        end
  in
  loop ()
;;

(* ==== *)

let defs = (Hashtbl.create tblsize : (string, definition) Hashtbl.t);;

let add_def d =
  match d with
  | DefReal (s, a, e) -> Hashtbl.add defs s d;
  | DefPseudo (h, s, a, e) -> Hashtbl.add defs s d;
;;
let has_def s = Hashtbl.mem defs s;;
let get_def s =
  let d = Hashtbl.find defs s in
  match d with
  | DefReal (s, params, body) -> (d, params, body)
  | DefPseudo (hyp, s, params, body) -> (d, params, body)
;;

(* ==== *)

let metas = (HE.create tblsize : int HE.t);;

let add_meta e i = HE.add metas e i;;
let remove_meta e = HE.remove metas e;;
let get_meta e = HE.find metas e;;

(* ==== *)

let branch_forms = (HE.create tblsize : int ref HE.t);;

let add_branches a =
  if Array.length a > 1 then begin
    let f e =
      try incr (HE.find branch_forms e)
      with Not_found -> HE.add branch_forms e (ref 1)
    in
    Array.iter (List.iter f) a
  end;
;;

let remove_branches a =
  if Array.length a > 1 then begin
    let f e =
      try
        let r = HE.find branch_forms e in
        decr r;
        if !r = 0 then HE.remove branch_forms e;
      with Not_found -> ()
    in
    Array.iter (List.iter f) a
  end;
;;

let get_branches l =
  let get_branches_1 n e =
    try n + !(HE.find branch_forms e)
    with Not_found -> n
  in
  List.fold_left get_branches_1 0 l
;;
    

(* ==== *)

let numforms = (HE.create tblsize : int HE.t);;

let cur_num = ref (-1);;
let get_number e =
  begin try HE.find numforms e
  with Not_found ->
    incr cur_num;
    HE.add numforms e !cur_num;
    !cur_num
  end
;;
