(*  Copyright 2004 INRIA  *)
Misc.version "$Id: ext_coqbool.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

(* Extension for Coq's "bool" type. *)
(* Symbols: Is_true, and_b, or_b, not_b, xor_b, _if_then_else *)

(* We essentially treat Is_true as if it weren't there. *)

open Expr;;
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

let add_formula e p =
  match e with
  | Eapp ("Is_true", [Eapp (f, _, _)], _) -> hadd istrue_forms f e;
  | Enot (Eapp ("Is_true", [Eapp (f, _, _)], _), _) -> hadd isfalse_forms f e;
  | _ -> ()
;;

let remove_formula e =
  match e with
  | Eapp ("Is_true", [Eapp (f, _, _)], _) -> hremove istrue_forms f;
  | Enot (Eapp ("Is_true", [Eapp (f, _, _)], _), _) -> hremove isfalse_forms f;
  | _ -> ()
;;

let find tbl s =
  try !(H.find tbl s)
  with Not_found -> []
;;

let wrong_arity s =
  if !Globals.warnings_flag then begin
    Printf.eprintf "Warning: defined symbol %s is used with wrong arity\n" s;
    flush stderr;
  end;
  ([], false)
;;

let istrue e = eapp ("Is_true", [e]);;

let make_notequal prio1 prio2 e f =
  match e, f with
  | Eapp ("Is_true", [e1], _), Enot (Eapp ("Is_true", [f1], _), _) ->
      let w1 = if has_meta e1 && has_meta f1 then Prio.weight_meta_neq else 0 in
      {
        nconc = [e; f];
        nrule = P_NotP (e, f);
        nprio = {
          Prio.shape = Prio.sh_p_notp;
          Prio.origin = min prio1.Prio.origin prio2.Prio.origin;
          Prio.weight1 = prio2.Prio.weight1 + Prio.weight_notequiv + w1;
          Prio.weight2 = prio1.Prio.weight1;
        };
        branches = [| [enot (eapp ("=", [e1; f1]))] |];
      }
  | _ -> assert false
;;

let newnodes e p =
  match e with
  | Eapp ("Is_true", [Eapp ("and_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "and_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eand (istrue e1, istrue e2)] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("or_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "or_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eor (istrue e1, istrue e2)] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("xor_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "xor_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eequiv (istrue e1, istrue e2))] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("not_b", [e1], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "not_b", [e1]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (istrue e1)] |];
          } ],
        true)

  | Enot (Eapp ("Is_true", [Eapp ("and_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notand_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eand (istrue e1, istrue e2))] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("or_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notor_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eor (istrue e1, istrue e2))] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("xor_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notxor_b", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eequiv (istrue e1, istrue e2)] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("not_b", [e1], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notnot_b", [e1]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [istrue e1] |];
          } ],
        true)

  | Eapp ("Is_true", [Evar ("true", _)], _) -> ([], true)
  | Enot (Eapp ("Is_true", [Evar ("false", _)], _), _) -> ([], true)

  | Eapp ("Is_true", [Evar ("false", _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "false", []);
            nprio = Prio.update p Prio.sh_close1 0 0;
            branches = [| |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Evar ("true", _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "nottrue", []);
            nprio = Prio.update p Prio.sh_close1 0 0;
            branches = [| |];
          } ],
        true)

  | Eapp ("Is_true", [Eapp (s, args, _)], _) when Index.has_def s ->
      begin try
        let (d, params, body) = Index.get_def s in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp ("Is_true", [substitute subst body]) in
        ( [ {
              nconc = [e];
              nrule = Ext ("coqbool", "definition", [e]);
              nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
              branches = [| [unfolded] |];
          } ],
          true)
      with
      | Invalid_argument "List.map2" -> wrong_arity s
      | Not_found -> assert false
      end

  | Enot (Eapp ("Is_true", [Eapp (s, args, _)], _), _) when Index.has_def s ->
      begin try
        let (d, params, body) = Index.get_def s in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp ("Is_true", [substitute subst body])) in
        ( [ {
              nconc = [e];
              nrule = Ext ("coqbool", "definition", [e]);
              nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
              branches = [| [unfolded] |];
          } ],
          true)
      with
      | Invalid_argument "List.map2" -> wrong_arity s
      | Not_found -> assert false
      end

  | Eapp ("Is_true", [Eapp (s, _, _)], _) ->
      let matches = find isfalse_forms s in
      let do_match x = make_notequal (Index.get_prio x) p e x in
      (List.map do_match matches, true)

  | Enot (Eapp ("Is_true", [Eapp (s, _, _)], _), _) ->
      let matches = find istrue_forms s in
      let do_match x = make_notequal (Index.get_prio x) p x e in
      (List.map do_match matches, true)

  | _ -> ([], false)
;;

let to_llproof mlp args =
  match mlp.mlrule with
  | Ext (_, "and_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "or_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "xor_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "not_b", [e1]) -> assert false (* FIXME TODO *)
  | Ext (_, "notand_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "notor_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "notxor_b", [e1; e2]) -> assert false (* FIXME TODO *)
  | Ext (_, "notnot_b", [e1]) -> assert false (* FIXME TODO *)
  | Ext (_, "false", []) -> assert false (* FIXME TODO *)
  | Ext (_, "nottrue", []) -> assert false (* FIXME TODO *)
  | Ext (_, "definition", [e1]) -> assert false (* FIXME TODO *)
  | _ -> assert false
;;

Extension.register {
  Extension.name = "coqbool";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.to_llproof = to_llproof;
};;
