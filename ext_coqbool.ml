(*  Copyright 2004 INRIA  *)
Version.add "$Id: ext_coqbool.ml,v 1.10 2004-10-18 16:53:28 doligez Exp $";;

(* Extension for Coq's "bool" type. *)
(* Symbols: Is_true, __g_and_b, __g_or_b, __g_not_b, __g_xor_b *)

(* We essentially treat Is_true as if it weren't there. *)

(* FIXME TODO:
   warning s'il y a une definition de Is_true, __g_and_b, etc.
*)

open Expr;;
open Misc;;
open Mlproof;;
open Node;;

module H = Hashtbl;;

let istrue_forms = (H.create 997 : (string, expr list ref) H.t);;
let isfalse_forms = (H.create 997 : (string, expr list ref) H.t);;

let hadd table key data =
  try
    let r = H.find table key in
    r := data :: !r;
  with Not_found ->
    H.add table key (ref [data]);
;;

let hremove table key =
  let r = H.find table key in
  r := List.tl !r;
;;

let add_formula e =
  match e with
  | Eapp ("Is_true", [Eapp (f, _, _)], _) -> hadd istrue_forms f e;
  | Eapp ("Is_true", [Emeta _], _) -> hadd istrue_forms "" e;
  | Enot (Eapp ("Is_true", [Eapp (f, _, _)], _), _) -> hadd isfalse_forms f e;
  | Enot (Eapp ("Is_true", [Emeta _], _), _) -> hadd isfalse_forms "" e;
  | _ -> ()
;;

let remove_formula e =
  match e with
  | Eapp ("Is_true", [Eapp (f, _, _)], _) -> hremove istrue_forms f;
  | Eapp ("Is_true", [Emeta _], _) -> hremove istrue_forms "";
  | Enot (Eapp ("Is_true", [Eapp (f, _, _)], _), _) -> hremove isfalse_forms f;
  | Enot (Eapp ("Is_true", [Emeta _], _), _) -> hremove isfalse_forms "";
  | _ -> ()
;;

let find tbl s =
  let exact = try !(H.find tbl s) with Not_found -> [] in
  let meta = try !(H.find tbl "") with Not_found -> [] in
  meta @@ exact
;;

let map_all tbl f =
  let do_list k d accu = List.map f !d @@ accu in
  H.fold do_list tbl []
;;

let wrong_arity s =
  if !Globals.warnings_flag then begin
    Printf.eprintf "Warning: defined symbol %s is used with wrong arity\n" s;
    flush stderr;
  end;
;;

let istrue e = eapp ("Is_true", [e]);;

let make_notequal depth e f =
  match e, f with
  | Eapp ("Is_true", [e1], _), Enot (Eapp ("Is_true", [f1], _), _) ->
      let branches = [| [enot (eapp ("=", [e1; f1]))] |] in
      {
        nconc = [e; f];
        nrule = P_NotP (e, f);
        nprio = Prio.make depth Prio.Correl branches;
        nbranches = branches;
      }
  | _ -> assert false
;;

let newnodes depth e =
  match e with
  | Eapp ("Is_true", [Eapp ("__g_and_b", [e1; e2], _)], _) ->
      let branches = [| [eand (istrue e1, istrue e2)] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "and", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp ("Is_true", [Eapp ("__g_or_b", [e1; e2], _)], _) ->
      let branches = [| [eor (istrue e1, istrue e2)] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "or", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp ("Is_true", [Eapp ("__g_xor_b", [e1; e2], _)], _) ->
      let branches = [| [enot (eequiv (istrue e1, istrue e2))] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "xor", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp ("Is_true", [Eapp ("__g_not_b", [e1], _)], _) ->
      let branches = [| [enot (istrue e1)] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "not", [e1]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp ("Is_true", [Eapp ("__g_and_b", [e1; e2], _)], _), _) ->
      let branches = [| [enot (eand (istrue e1, istrue e2))] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "notand", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp ("Is_true", [Eapp ("__g_or_b", [e1; e2], _)], _), _) ->
      let branches = [| [enot (eor (istrue e1, istrue e2))] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "notor", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp ("Is_true", [Eapp ("__g_xor_b", [e1; e2], _)], _), _) ->
      let branches = [| [eequiv (istrue e1, istrue e2)] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "notxor", [e1; e2]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp ("Is_true", [Eapp ("__g_not_b", [e1], _)], _), _) ->
      let branches = [| [istrue e1] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "notnot", [e1]);
        nprio = Prio.make depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp ("Is_true", [Evar ("true", _)], _) -> [Stop]
  | Enot (Eapp ("Is_true", [Evar ("false", _)], _), _) -> [Stop]

  | Eapp ("Is_true", [Evar ("false", _)], _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "false", []);
        nprio = Prio.make depth Prio.Close [| |];
        nbranches = [| |];
      }; Stop ]
  | Enot (Eapp ("Is_true", [Evar ("true", _)], _), _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("coqbool", "nottrue", []);
        nprio = Prio.make depth Prio.Close [| |];
        nbranches = [| |];
      }; Stop ]
(* FIXME TODO: faire nrule = Ext, et etendre la traduction
   pour que les pseudo-defs marchent correctement
*)
  | Eapp ("Is_true", [Eapp (s, args, _)], _) when Index.has_def s ->
      begin try
        let (d, params, body) = Index.get_def s in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp ("Is_true", [substitute subst body]) in
        let branches = [| [unfolded] |] in
        [ Node {
          nconc = [e];
          nrule = Definition (d, e, unfolded);
          nprio = Prio.make depth Prio.Alpha1 branches;
          nbranches = branches;
        }; Stop ]
      with
        | Invalid_argument "List.map2" -> wrong_arity s; []
        | Not_found -> assert false
      end
  | Enot (Eapp ("Is_true", [Eapp (s, args, _)], _), _) when Index.has_def s ->
      begin try
        let (d, params, body) = Index.get_def s in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp ("Is_true", [substitute subst body])) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [e];
            nrule = Definition (d, e, unfolded);
            nprio = Prio.make depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
        | Invalid_argument "List.map2" -> wrong_arity s; []
        | Not_found -> assert false
      end
  | Eapp ("Is_true", [Eapp (s, _, _)], _) ->
      let matches = find isfalse_forms s in
      let do_match x = Node (make_notequal depth e x) in
      (List.map do_match matches) @ [Stop]
  | Eapp ("Is_true", [Emeta _], _) ->
      let do_match x = Node (make_notequal depth e x) in
      map_all isfalse_forms do_match
  | Enot (Eapp ("Is_true", [Eapp (s, _, _)], _), _) ->
      let matches = find istrue_forms s in
      let do_match x = Node (make_notequal depth x e) in
      (List.map do_match matches) @ [Stop]
  | Enot (Eapp ("Is_true", [Emeta _], _), _) ->
      let do_match x = Node (make_notequal depth x e) in
      map_all istrue_forms do_match
  | _ -> []
;;

let to_llargs tr_prop tr_term r =
  match r with
  | Ext (_, "and", [e1; e2]) ->
      let h = tr_prop (eand (istrue e1, istrue e2)) in
      let c = tr_prop (istrue (eapp ("__g_and_b", [e1; e2]))) in
      ("zenon_coqbool_and", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "or", [e1; e2]) ->
      let h = tr_prop (eor (istrue e1, istrue e2)) in
      let c = tr_prop (istrue (eapp ("__g_or_b", [e1; e2]))) in
      ("zenon_coqbool_or", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "xor", [e1; e2]) ->
      let h = tr_prop (enot (eequiv (istrue e1, istrue e2))) in
      let c = tr_prop (istrue (eapp ("__g_xor_b", [e1; e2]))) in
      ("zenon_coqbool_xor", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "not", [e1]) ->
      let h = tr_prop (enot (istrue e1)) in
      let c = tr_prop (istrue (eapp ("__g_not_b", [e1]))) in
      ("zenon_coqbool_not", [tr_term e1], [c], [ [h] ])
  | Ext (_, "notand", [e1; e2]) ->
      let h = tr_prop (enot (eand (istrue e1, istrue e2))) in
      let c = tr_prop (enot (istrue (eapp ("__g_and_b", [e1; e2])))) in
      ("zenon_coqbool_notand", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "notor", [e1; e2]) ->
      let h = tr_prop (enot (eor (istrue e1, istrue e2))) in
      let c = tr_prop (enot (istrue (eapp ("__g_or_b", [e1; e2])))) in
      ("zenon_coqbool_notor", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "notxor", [e1; e2]) ->
      let h = tr_prop (eequiv (istrue e1, istrue e2)) in
      let c = tr_prop (enot (istrue (eapp ("__g_xor_b", [e1; e2])))) in
      ("zenon_coqbool_notxor", [tr_term e1; tr_term e2], [c], [ [h] ])
  | Ext (_, "notnot", [e1]) ->
      let h = tr_prop (istrue e1) in
      let c = tr_prop (enot (istrue (eapp ("__g_not_b", [e1])))) in
      ("zenon_coqbool_notnot", [tr_term e1], [c], [ [h] ])
  | Ext (_, "false", []) ->
      let c = tr_prop (istrue (evar "false")) in
      ("zenon_coqbool_false", [], [c], []);
  | Ext (_, "nottrue", []) ->
      let c = tr_prop (enot (istrue (evar "true"))) in
      ("zenon_coqbool_nottrue", [], [c], []);
  | _ -> assert false
;;

let to_llproof tr_prop tr_term mlp args =
  let (name, meta, con, hyp) = to_llargs tr_prop tr_term mlp.mlrule in
  let (subs, exts) = List.split (Array.to_list args) in
  let ext = List.fold_left Expr.union [] exts in
  let extras = Expr.diff ext mlp.mlconc in
  let nn = {
      Llproof.conc = List.map tr_prop (extras @@ mlp.mlconc);
      Llproof.rule = Llproof.Rextension (name, meta, con, hyp);
      Llproof.hyps = subs;
    }
  in (nn, extras)
;;

Extension.register {
  Extension.name = "coqbool";
  Extension.newnodes = (fun depth e -> lazy (newnodes depth e));
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.to_llproof = to_llproof;
};;
