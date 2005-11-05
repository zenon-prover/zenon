(*  Copyright 2004 INRIA  *)
Version.add "$Id: index.ml,v 1.6 2005-11-05 11:13:17 doligez Exp $";;

open Expr;;
open Misc;;
open Mlproof;;
open Printf;;

let ( === ) = ( = );;
let ( = ) = ();;
let string_equal x y = String.compare x y == 0;;

let tblsize = 997;;  (* reduce to 17 for debugging *)

module HE = Hashtbl.Make (Expr);;

let allforms = (HE.create tblsize : int HE.t);;

type sym_table = (string, expr list ref) Hashtbl.t;;

let posforms = (Hashtbl.create tblsize : sym_table);;
let negforms = (Hashtbl.create tblsize : sym_table);;

type formula_rec = {
  mutable present : bool;
  mutable proofs : (Mlproof.proof * int ref * formula_rec array) list;
};;
let proofs = (HE.create tblsize : formula_rec HE.t);;
let new_forms = ref [];;

exception No_head;;

type head = Sym of string | Tau of expr | Wild;;

let get_head e =
  match e with
  | Eapp (s, _, _) | Evar (s, _)
    -> Sym s
  | Emeta _ -> Wild
  | Etau _ -> Tau e
  | _ -> raise No_head
;;

let add_element tbl k v =
  try
    let lr = Hashtbl.find tbl k in
    lr := v :: !lr
  with Not_found ->
    Hashtbl.add tbl k (ref [v]);
;;

let remove_element tbl k v =
  try
    let lr = Hashtbl.find tbl k in
    match !lr with
    | [] -> assert false
    | [h] -> Hashtbl.remove tbl k;
    | h::t -> assert (Expr.equal h v); lr := t;
  with Not_found -> assert false
;;

(* ==== *)

type direction = Left | Right | Both;;

type trans_table = (string * head, expr list ref) Hashtbl.t;;

let pos_trans_left = (Hashtbl.create tblsize : trans_table);;
let pos_trans_right = (Hashtbl.create tblsize : trans_table);;
let pos_trans_key = (HE.create tblsize : direction HE.t);;

let rec do_trans action e dir =
  match dir, e with
  | Left, Eapp (r, [e1; e2], _) ->
      action pos_trans_left (r, get_head e1) e;
  | Right, Eapp (r, [e1; e2], _) ->
      action pos_trans_right (r, get_head e2) e;
  | Both, Eapp (r, [e1; e2], _) ->
      action pos_trans_left (r, get_head e1) e;
      action pos_trans_right (r, get_head e2) e;
  | _ -> assert false
;;

let add_trans e dir =
  HE.add pos_trans_key e dir;
  do_trans add_element e dir;
;;

let try_find tbl k =
  try !(Hashtbl.find tbl k)
  with Not_found -> []
;;

let find_all_rel tbl rel =
  let f (r, _) elr accu =
    if string_equal r rel then !elr @@ accu else accu
  in
  Hashtbl.fold f tbl []
;;

let find_trans_left rel head =
  if head === Wild
  then find_all_rel pos_trans_left rel
  else try_find pos_trans_left (rel, head)
       @@ (try_find pos_trans_left (rel, Wild))
;;

let find_trans_right rel head =
  if head === Wild
  then find_all_rel pos_trans_right rel
  else try_find pos_trans_right (rel, head)
       @@ (try_find pos_trans_right (rel, Wild))
;;

let find_trans_leftonly rel head =
  let l = find_trans_left rel head in
  List.filter (fun e -> (HE.find pos_trans_key e) === Left) l
;;

let find_trans_rightonly rel head =
  let l = find_trans_right rel head in
  List.filter (fun e -> (HE.find pos_trans_key e) === Right) l
;;

let find_all_head tbl head =
  let f (_, h) elr accu =
    match head, h with
    | Wild, _ | _, Wild -> !elr @@ accu
    | h1, h2 when h1 === h2 -> !elr @@ accu
    | _, _ -> accu
  in
  Hashtbl.fold f tbl []
;;

let find_all_trans_leftonly head =
  let l = find_all_head pos_trans_left head in
  List.filter (fun e -> (HE.find pos_trans_key e) === Left) l
;;

let find_all_trans_rightonly head =
  let l = find_all_head pos_trans_right head in
  List.filter (fun e -> (HE.find pos_trans_key e) === Right) l
;;

let remove_trans e =
  try
    let dir = HE.find pos_trans_key e in
    do_trans remove_element e dir;
    HE.remove pos_trans_key e;
  with Not_found -> ()
;;

let neg_trans_left = (Hashtbl.create tblsize : trans_table);;
let neg_trans_right = (Hashtbl.create tblsize : trans_table);;
let neg_trans_key = (HE.create tblsize : unit HE.t);;

type head_table = (head, expr list ref) Hashtbl.t;;

let all_neg_trans_left = (Hashtbl.create tblsize : head_table);;
let all_neg_trans_right = (Hashtbl.create tblsize : head_table);;

let add_negtrans e =
  match e with
  | Enot (Eapp (r, [e1; e2], _), _) ->
      begin try
        add_element neg_trans_left (r, get_head e1) e;
        add_element all_neg_trans_left (get_head e1) e;
      with No_head -> ()
      end;
      begin try
        add_element neg_trans_right (r, get_head e2) e;
        add_element all_neg_trans_right (get_head e2) e;
      with No_head -> ()
      end;
      HE.add neg_trans_key e ();
  | _ -> assert false;
;;

let remove_negtrans e =
  if HE.mem neg_trans_key e then begin
    match e with
    | Enot (Eapp (r, [e1; e2], _), _) ->
        begin try
          remove_element neg_trans_left (r, get_head e1) e;
          remove_element all_neg_trans_left (get_head e1) e;
        with No_head -> ()
        end;
        begin try
          remove_element neg_trans_right (r, get_head e2) e;
          remove_element all_neg_trans_right (get_head e2) e;
        with No_head -> ()
        end;
        HE.remove neg_trans_key e;
    | _ -> assert false;
  end;
;;

let find_negtrans_left rel head =
  assert (head <> Wild);
  try_find neg_trans_left (rel, head)
;;

let find_negtrans_right rel head =
  assert (head <> Wild);
  try_find neg_trans_right (rel, head)
;;

let find_all_negtrans_left head =
  assert (head <> Wild);
  try_find all_neg_trans_left head
;;

let find_all_negtrans_right head =
  assert (head <> Wild);
  try_find all_neg_trans_right head
;;

let find_all_negtrans () =
  let f k _ l = k::l in
  HE.fold f neg_trans_key []
;;

(* ==== *)

let act_head action tbl key v =
  try
    match get_head key with
    | Sym s -> action tbl s v
    | Tau e -> action tbl "t." v
    | Wild -> action tbl "" v
  with No_head -> ()
;;

let negpos action e =
  match e with
  | Enot (f, _) -> act_head action negforms f e;
  | f -> act_head action posforms f e;
;;

let cur_num_forms = ref 0;;

let add e g =
  HE.add allforms e g;
  incr cur_num_forms;
  if !cur_num_forms > !Globals.top_num_forms
  then Globals.top_num_forms := !cur_num_forms;
  negpos add_element e;
  begin try (HE.find proofs e).present <- true with Not_found -> (); end;
  new_forms := e :: !new_forms;
;;

let remove e =
  decr cur_num_forms;
  remove_trans e;
  remove_negtrans e;
  negpos remove_element e;
  HE.remove allforms e;
  begin try (HE.find proofs e).present <- false with Not_found -> (); end;
;;

let get_all () = HE.fold (fun e _ l -> e::l) allforms [];;

let member e = HE.mem allforms e;;

let get_goalness e = HE.find allforms e;;

let find_pos s =
  try !(Hashtbl.find posforms s)
  with Not_found -> []
;;

let find_neg s =
  try !(Hashtbl.find negforms s)
  with Not_found -> []
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
  let recs = Array.of_list (List.map get_record p.mlconc) in
  suspects := [(p, ref 0, recs)] :: !suspects;
;;

(* FIXME essayer:
   changer la structure de donnees pour utiliser des refcounts
*)

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
    | ((p, cur, recs) as lem :: t1) :: t2 ->
        begin try
          for i = !cur to Array.length recs - 1 do
            if not recs.(i).present then begin
              suspects := t1 :: t2;
              recs.(i).proofs <- lem :: recs.(i).proofs;
              cur := i+1;
              raise Exit;
            end
          done;
          for i = 0 to !cur-1 do
            if not recs.(i).present then begin
              suspects := t1 :: t2;
              recs.(i).proofs <- lem :: recs.(i).proofs;
              cur := i+1;
              raise Exit;
            end
          done;
          Some p
        with Exit -> loop ()
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

let cur_num = ref (-1);;
let numforms = (HE.create tblsize : int HE.t);;
let formnums = ref ([| |] : expr array);;
let dummy = evar " *** Index.dummy *** ";;

let ext_set tbl i x =
  while i >= Array.length !tbl do
    let len = Array.length !tbl in
    let new_len = 2 * len + 1 in
    let new_tbl = Array.make new_len dummy in
    Array.blit !tbl 0 new_tbl 0 len;
    tbl := new_tbl;
  done;
  !tbl.(i) <- x;
;;

let get_number e =
  begin try HE.find numforms e
  with Not_found ->
    incr cur_num;
    HE.add numforms e !cur_num;
    ext_set formnums !cur_num e;
    !cur_num
  end
;;

let get_formula i =
  if i < 0 || i >= Array.length !formnums then raise Not_found;
  if !formnums.(i) == dummy then raise Not_found;
  !formnums.(i)
;;
