(*  Copyright 2004 INRIA  *)
Version.add "$Id: ext_coqbool.ml,v 1.5 2004-05-28 08:10:51 doligez Exp $";;

(* Extension for Coq's "bool" type. *)
(* Symbols: Is_true, __g_and_b, __g_or_b, __g_not_b, __g_xor_b, _if_then_else *)

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
  | Eapp ("Is_true", [Eapp ("__g_and_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "and", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eand (istrue e1, istrue e2)] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("__g_or_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "or", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eor (istrue e1, istrue e2)] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("__g_xor_b", [e1; e2], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "xor", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eequiv (istrue e1, istrue e2))] |];
          } ],
        true)
  | Eapp ("Is_true", [Eapp ("__g_not_b", [e1], _)], _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "not", [e1]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (istrue e1)] |];
          } ],
        true)

  | Enot (Eapp ("Is_true", [Eapp ("__g_and_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notand", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eand (istrue e1, istrue e2))] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("__g_or_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notor", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [enot (eor (istrue e1, istrue e2))] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("__g_xor_b", [e1; e2], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notxor", [e1; e2]);
            nprio = Prio.update p Prio.sh_def Prio.weight_def 0;
            branches = [| [eequiv (istrue e1, istrue e2)] |];
          } ],
        true)
  | Enot (Eapp ("Is_true", [Eapp ("__g_not_b", [e1], _)], _), _) ->
      ( [ {
            nconc = [e];
            nrule = Ext ("coqbool", "notnot", [e1]);
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
              nrule = Definition (d, e, unfolded);
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
              nrule = Definition (d, e, unfolded);
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

let get_1 = function
  | [x] -> x
  | _ -> assert false
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
  {
    Llproof.conc = List.map tr_prop mlp.mlconc;
    Llproof.rule = Llproof.Rextension (name, meta, con, hyp);
    Llproof.hyps = Array.to_list args;
  }
;;

Extension.register {
  Extension.name = "coqbool";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.to_llproof = to_llproof;
};;
