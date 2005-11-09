(*  Copyright 2002 INRIA  *)
Version.add "$Id: prove.ml,v 1.14 2005-11-09 15:18:24 doligez Exp $";;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Printf;;

let ( =%= ) = ( = );;
let ( = ) = Expr.equal;;

module OrderedInt = struct
  type t = int;;
  let compare = Pervasives.compare;;
end;;

module IntMap = Map.Make (OrderedInt);;

type merge_status =
  | Main of int list      (* variables that depend on this one *)
  | Ref of int            (* which variable this one depends on *)
;;

type inst =
  | Ground of expr
  | Partial of string * int
;;

type inst_info = {
  merge : merge_status;
  formulas : expr list;
  terms : inst list;
};;

type state = {
  queue : queue;
  inst : inst_info IntMap.t;
  (* forms : indexes of the current branch's formulas *)
  (* cur_depth : int; *)
  (* extended_state : state records of the active extensions *)
};;

type branch_state =
  | Open
  | Closed of proof
;;

type frame = {
  node : node;
  state : state;
  brst : branch_state array;
  curbr : int;
};;

(***************)

let cur_depth = ref 0;;
let top_depth = ref 0;;

(****************)

let complement fm =
  match fm with
  | Enot (p, _) -> (p, p)
  | p -> (enot (p), p)
;;

let rec replace_meta m va e =
  match e with
  | Evar _ -> e
  | Emeta _ -> if Expr.equal e m then va else e
  | Eapp (s, args, _) -> eapp (s, List.map (replace_meta m va) args)
  | Enot (f, _) -> enot (replace_meta m va f)
  | Eand (f, g, _) -> eand (replace_meta m va f, replace_meta m va g)
  | Eor (f, g, _) -> eor (replace_meta m va f, replace_meta m va g)
  | Eimply (f, g, _) -> eimply (replace_meta m va f, replace_meta m va g)
  | Eequiv (f, g, _) -> eequiv (replace_meta m va f, replace_meta m va g)
  | Etrue -> e
  | Efalse -> e
  | Eall (v, t, f, o, _) -> eall (v, t, replace_meta m va f, o)
  | Eex (v, t, f, o, _) -> eex (v, t, replace_meta m va f, o)
  | Etau (v, t, f, _) -> etau (v, t, replace_meta m va f)
  | Elam (v, t, f, _) -> elam (v, t, replace_meta m va f)
;;

let is_meta = function
  | Emeta _ -> true
  | _ -> false
;;

let rec pure_meta l =
  let rec all_different l =
    match l with
    | [] -> true
    | h::t -> not (List.exists (Expr.equal h) t)
              && all_different t
  in
  match l with
  | [] -> false
  | [Eapp (_, l1, _)] -> pure_meta l1
  | _ -> List.for_all is_meta l && all_different l
;;

(****************)

let add_node st n =
  { st with queue = insert st.queue n }
;;

let add_node_list st ns =
  List.fold_left add_node st ns
;;

let get_info st m =
  try IntMap.find m st.inst
  with Not_found -> { merge = Main [m]; formulas = []; terms = [] }
;;

let rec get_ref st m =
  let info = get_info st m in
  match info.merge with
  | Main l -> m
  | Ref mm -> get_ref st mm
;;

let add_inst_term st m inst =
  let info = get_info st m in
  let info1 = { info with terms = inst :: info.terms } in
  { st with inst = IntMap.add m info1 st.inst }
;;

let add_inst_form st m form =
  let info = get_info st m in
  let info1 = { info with formulas = form :: info.formulas } in
  { st with inst = IntMap.add m info1 st.inst }
;;

let get_formulas st m = (get_info st m).formulas;;
let get_terms st m = (get_info st m).terms;;

let make_one_inst inst fm =
  match inst with
  | Partial (sym, arity) ->
      let vars = list_init arity newvar in
      let term = eapp (sym, vars) in
      begin match fm with
      | Eall (v, t, p, m, _) ->
          let n = all_list vars (Expr.substitute [(v, term)] p) in
          let branches = [| [n] |] in
          {
            nconc = [fm];
            nrule = AllPartial (fm, sym, arity);
            nprio = Inst m;
            nbranches = branches;
          }
      | Enot (Eex (v, t, p, m, _), _) ->
          let n = enot (ex_list vars (Expr.substitute [(v, term)] p)) in
          let branches = [| [n] |] in
          {
            nconc = [fm];
            nrule = NotExPartial (fm, sym, arity);
            nprio = Inst m;
            nbranches = branches;
          }
      | _ -> assert false
      end
  | Ground (term) ->
      begin match fm with
      | Eall (v, t, p, m, _) ->
          let n = Expr.substitute [(v, term)] p in
          let branches = [| [n] |] in
          {
            nconc = [fm];
            nrule = All (fm, term);
            nprio = Inst m;
            nbranches = branches;
          }
      | Enot (Eex (v, t, p, m, _), _) ->
          let n = enot (Expr.substitute [(v, term)] p) in
          let branches = [| [n] |] in
          {
            nconc = [fm];
            nrule = NotEx (fm, term);
            nprio = Inst m;
            nbranches = branches;
          }
      | _ -> assert false
      end
;;

let inst_equal i1 i2 =
  match i1, i2 with
  | Ground e1, Ground e2 -> e1 = e2
  | Partial (s1, a1), Partial (s2, a2) -> s1 =%= s2 && a1 =%= a2
  | _, _ -> false
;;

let add_inst st mm i =
  let info = get_info st mm in
  if List.exists (inst_equal i) info.terms then
    st
  else begin
    let nodes = List.map (make_one_inst i) info.formulas in
    let st1 = add_inst_term st mm i in
    add_node_list st1 nodes
  end
;;

(* [make_inst st m e]
   update the state st with the instantiation m <- e
   return the new state and a flag:
     true if the instantiation is full, false if partial
*)

let make_inst st m e =
  let mm = get_ref st m in
  (* FIXME TODO: canoniser les metavariables de e *)
  if Expr.occurs_as_meta mm e then begin
    match e with
    | Eapp (sym, args, _) ->
        (add_inst st mm (Partial (sym, List.length args)), false)
    | Etau _ ->
        (add_inst st mm (Ground e), true)
    | Emeta _ ->
        (st, false)
    | _ -> assert false
  end else begin
    (add_inst st mm (Ground e), true)
  end
;;

(* [make_inst_fm st m fm]
   update the state st with the instantiations of fm by the insts of m
   and add fm to the forms of m
*)
let make_inst_fm st m fm =
  let mm = get_ref st m in
  let info = get_info st mm in
  if List.exists (fun x -> x = fm) info.formulas then
    st
  else begin
    let nodes = List.map (fun i -> make_one_inst i fm) info.terms in
    let st1 = add_inst_form st mm fm in
    add_node_list st1 nodes
  end
;;

let make_cross_inst is fs =
  let f fs i = List.map (make_one_inst i) fs in
  List.flatten (List.map (f fs) is)
;;

let merge_metas st m1 m2 =
(*
eprintf "merge %d with %d\n" m1 m2; flush stderr;
*)
  let mm1 = get_ref st m1 in
  let mm2 = get_ref st m2 in
  let info1 = get_info st mm1 in
  let info2 = get_info st mm2 in
  let l1 = match info1.merge with Main l -> l | _ -> assert false in
  let l2 = match info2.merge with Main l -> l | _ -> assert false in
  if mm1 =%= mm2 then st
  else
    let (mmx, lx, infox, mmy, ly, infoy) =
      if mm1 < mm2
      then (mm1, l1, info1, mm2, l2, info2)
      else (mm2, l2, info2, mm1, l1, info1)
    in
    let i = Ground (emeta (mmx)) in
    let nodes_m = List.map (make_one_inst i) infoy.formulas in
    let f x = not (List.exists (inst_equal x) infox.terms) in
    let termy = List.filter f infoy.terms in
    let nodes_xy = make_cross_inst infox.terms infoy.formulas in
    let nodes_yx = make_cross_inst termy infox.formulas in
    let infoxx = {
      merge = Main (ly @@ lx);
      formulas = infoy.formulas @@ infox.formulas;
      terms = termy @@ infox.terms;
    } in
    let instx = IntMap.add mmx infoxx st.inst in
    let f inst m =
      let ii = { (get_info st m) with merge = Ref mmx } in
      IntMap.add m ii inst
    in
    let insty = List.fold_left f instx ly in
    let st1 = add_node_list st nodes_m in
    let st2 = add_node_list st1 nodes_xy in
    let st3 = add_node_list st2 nodes_yx in
    { st3 with inst = insty }
;;

(* [make_inequals l1 l2]
   l1 and l2 are the same length
   returns the pairwise inequalities between corresponding elements of l1 and l2
   return it as a list of lists
*)
let rec make_inequals_aux l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | h1::t1, h2::t2 ->
      [enot (eapp ("=", [h1; h2]))] :: make_inequals_aux t1 t2
  | _, _ -> assert false
;;
let make_inequals l1 l2 = Array.of_list (make_inequals_aux l1 l2);;

let arity_warning s =
  Error.warn (sprintf "symbol %s is used with inconsistent arities" s);
;;

let make_notequiv st sym p np =
  match p, np with
  | Eapp (s1, args1, _), Enot (Eapp (s2, args2, _), _) ->
      assert (s1 =%= s2);
      if sym && List.length args2 != 2
         || List.length args1 <> List.length args2
      then (arity_warning s1; st)
      else
        let myrule = if sym then P_NotP_sym (s1, p, np) else P_NotP (p, np) in
        let myargs1 = if sym then List.rev args1 else args1 in
        let branches = make_inequals myargs1 args2 in
        add_node st {
          nconc = [p; np];
          nrule = myrule;
          nprio = Arity;
          nbranches = branches;
        }
  | _ -> assert false
;;

(* [is_conj f m]:
   f is a n-ary conjunctive formula
   return 0 if n >= m; return m-n otherwise
*)
let rec is_conj f m =
  if m <= 0 then 0 else
  match f with
  | Eand (a, b, _) -> is_conj b (is_conj a m)
  | Enot (a, _) -> is_disj a m
  | _ -> m-1

and is_disj f m =
  if m <= 0 then 0 else
  match f with
  | Eor (a, b, _) -> is_disj b (is_disj a m)
  | Eimply (a, b, _) -> is_disj b (is_conj a m)
  | Enot (a, _) -> is_conj a m
  | _ -> m-1
;;

let rec decomp_conj neg accu f =
  match f with
  | Eand (a, b, _) -> decomp_conj neg (decomp_conj neg accu b) a
  | Enot (a, _) -> decomp_disj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu

and decomp_disj neg accu f =
  match f with
  | Eor (a, b, _) -> decomp_disj neg (decomp_disj neg accu b) a
  | Eimply (a, b, _) -> decomp_conj (not neg) (decomp_disj neg accu b) a
  | Enot (a, _) -> decomp_conj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu
;;

let newnodes_absurd st fm =
  match fm with
  | Enot (p, _) when Index.member p -> add_node st {
      nconc = [fm; p];
      nrule = Close (p);
      nprio = Arity;
      nbranches = [| |];
    }, true
  | p when Index.member (enot p) -> add_node st {
      nconc = [p; enot p];
      nrule = Close (p);
      nprio = Arity;
      nbranches = [| |];
    }, true
  | _ -> st, false
;;

let newnodes_closure st fm =
  match fm with
  | Efalse -> add_node st {
      nconc = [fm];
      nrule = False;
      nprio = Arity;
      nbranches = [| |];
    }, true
  | Enot (Etrue, _) -> add_node st {
      nconc = [fm];
      nrule = NotTrue;
      nprio = Arity;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [a; b], _), _) when Eqrel.refl s && Expr.equal a b ->
    add_node st {
      nconc = [fm];
      nrule = Close_refl (s, a);
      nprio = Arity;
      nbranches = [| |];
    }, true
  | Eapp (s, [e1; e2], _)
    when Eqrel.sym s && Index.member (enot (eapp (s, [e2; e1]))) ->
    add_node st {
      nconc = [fm; (enot (eapp (s, [e2; e1])))];
      nrule = Close_sym (s, e1, e2);
      nprio = Arity;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [e1; e2], _), _)
    when Eqrel.sym s && Index.member (eapp (s, [e2; e1])) ->
    add_node st {
      nconc = [fm; (eapp (s, [e2; e1]))];
      nrule = Close_sym (s, e2, e1);
      nprio = Arity;
      nbranches = [| |];
    }, true
  | _ -> st, false
;;

let newnodes_jtree st fm =
  match fm with
  | Eand _ | Enot (Eor _, _) | Enot (Eimply _, _)
    when is_conj fm 3 == 0 ->
      let branches = [| decomp_conj false [] fm |] in
      add_node st {
        nconc = [fm];
        nrule = ConjTree fm;
        nprio = Arity;
        nbranches = branches;
      }, true
  | Eor _ | Enot (Eand _, _) | Eimply _
    when is_disj fm 3 == 0 ->
      let forms = Array.of_list (decomp_disj false [] fm) in
      let branches = Array.map (fun x -> [x]) forms in
      add_node st {
        nconc = [fm];
        nrule = DisjTree fm;
        nprio = Arity;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_alpha st fm =
  match fm with
  | Enot (Enot (a, _), _) ->
      let branches = [| [a] |] in
      add_node st {
        nconc = [fm];
        nrule = NotNot (a);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Eand (a, b, _) ->
      let branches = [| [a; b] |] in
      add_node st {
        nconc = [fm];
        nrule = And (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eor (a, b, _), _) ->
      let branches = [| [enot (a); enot (b)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotOr (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eimply (a, b, _), _) ->
      let branches = [| [a; enot (b)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotImpl (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_beta st fm =
  match fm with
  | Eor (a, b, _) ->
      let branches = [| [a]; [b] |] in
      add_node st {
        nconc = [fm];
        nrule = Or (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Eimply (a, b, _) ->
      let branches = [| [enot (a)]; [b] |] in
      add_node st {
        nconc = [fm];
        nrule = Impl (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eand (a, b, _), _) ->
      let branches = [| [enot (a)]; [enot (b)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotAnd (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Eequiv (a, b, _) ->
      let branches = [| [enot (a); enot (b)]; [a; b] |] in
      add_node st {
        nconc = [fm];
        nrule = Equiv (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eequiv (a, b, _), _) ->
      let branches = [| [enot (a); b]; [a; enot (b)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotEquiv (a, b);
        nprio = Arity;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_delta st fm =
  match fm with
  | Eex (v, t, p, _, _) ->
      let branches = [| [Expr.substitute [(v, etau (v, t, p))] p] |] in
      add_node st {
        nconc = [fm];
        nrule = Ex (fm);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eall (v, t, p, _, _), _) ->
      let np = enot (p) in
      let branches = [| [Expr.substitute [(v, etau (v, t, np))] np] |] in
      add_node st {
        nconc = [fm];
        nrule = NotAll (fm);
        nprio = Arity;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_gamma st fm =
  match fm with
  | Eall (v, t, p, m, _) ->
      let mm = get_ref st m in
      let w = emeta (mm) in
      let branches = [| [Expr.substitute [(v, w)] p] |] in
      let st1 = make_inst_fm st mm fm in
      add_node st1 {
        nconc = [fm];
        nrule = All (fm, w);
        nprio = Arity;
        nbranches = branches;
      }, true
  | Enot (Eex (v, t, p, m, _), _) ->
      let mm = get_ref st m in
      let w = emeta (mm) in
      let branches = [| [enot (Expr.substitute [(v, w)] p)] |] in
      let st1 = make_inst_fm st mm fm in
      add_node st1 {
        nconc = [fm];
        nrule = NotEx (fm, w);
        nprio = Arity;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_unfold st fm =
  match fm with
  | Eapp (p, args, _) when Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = substitute subst body in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end
  | Enot (Eapp (p, args, _), _) when Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (substitute subst body) in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end
  | Eapp (s, [Eapp (p, args, _); e], _) when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp (s, [substitute subst body; e]) in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end
  | Eapp (s, [e; Eapp (p, args, _)], _) when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp (s, [e; substitute subst body]) in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end
  | Enot (Eapp (s, [Eapp (p, args, _); e], _), _)
    when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp (s, [substitute subst body; e])) in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end
  | Enot (Eapp (s, [e; Eapp (p, args, _)], _), _)
    when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp (s, [e; substitute subst body])) in
        let branches = [| [unfolded] |] in
        add_node st {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Arity;
            nbranches = branches;
        }, true
      with
      | Invalid_argument "List.map2" -> arity_warning p; (st, false)
      | Not_found -> assert false
      end

  | Evar (v, _) when Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let branches = [| [body] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, body);
          nprio = Arity;
          nbranches = branches;
        }, true
  | Enot (Evar (v, _), _) when Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot body in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Arity;
          nbranches = branches;
        }, true
  | Eapp (s, [Evar (v, _); e], _) when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = eapp (s, [body; e]) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Arity;
          nbranches = branches;
        }, true
  | Eapp (s, [e; Evar (v, _)], _) when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = eapp (s, [e; body]) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Arity;
          nbranches = branches;
        }, true
  | Enot (Eapp (s, [Evar (v, _); e], _), _)
    when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot (eapp (s, [body; e])) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Arity;
          nbranches = branches;
        }, true
  | Enot (Eapp (s, [e; Evar (v, _)], _), _)
    when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot (eapp (s, [e; body])) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; (st, false))
      else
        add_node st {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Arity;
          nbranches = branches;
        }, true
  | _ -> st, false
;;

let newnodes_refl st fm =
  match fm with
  | Enot (Eapp (s, [e1; e2], _), _) when s <> "=" && Eqrel.refl s ->
      let branches = [| [enot (eapp ("=", [e1; e2]))] |] in
      add_node st {
        nconc = [fm];
        nrule = Refl (s, e1, e2);
        nprio = Arity;
        nbranches = branches;
      }, false

  | Enot (Eapp ("=", [Emeta (m1, _); Emeta (m2, _)], _), _) ->
      merge_metas st m1 m2, true

  | Enot (Eapp ("=", [Emeta (m, _); e], _), _) -> make_inst st m e
  | Enot (Eapp ("=", [e; Emeta (m, _)], _), _) -> make_inst st m e

  | _ -> st, false
;;

let newnodes_match_congruence st fm =
  match fm with
  | Enot (Eapp ("=", [(Eapp (f1, a1, _) as e1);
                      (Eapp (f2, a2, _) as e2)], _), _)
    when f1 =%= f2 ->
      if List.length a1 == List.length a2 then begin
        let branches = make_inequals a1 a2 in
        add_node st {
          nconc = [fm];
          nrule = NotEqual (e1, e2);
          nprio = Arity;
          nbranches = branches;
        }, false
      end else (arity_warning f1; (st, false))
(*
  FIXME determiner ci c'est utile...
  | Enot (Eapp ("=", [Etau (v1, t1, f1, _); Etau (v2, t2, f2, _)], _), _) ->
      let f2a = Expr.substitute [(v2, v1)] f2 in
      let u = Expr.preunify f1 f2a in
      let f (st, _) (m, e) = make_inst st m e in
      List.fold_left f (st, false) u
*)
  | _ -> st, false
;;

let mknode_trans sym e1 e2 =
  let (r, a, b, c, d) =
    match e1, e2 with
    | Eapp (r, [a; b], _), Enot (Eapp (rr, [c; d], _), _) ->
      assert (r =%= rr);
      (r, a, b, c, d)
    | _, _ -> assert false
  in
  let (x, y, z, t) = if sym then (d, a, b, c) else (c, a, b, d) in
  let branches = [|
    [enot (eapp ("=", [x; y])); enot (eapp (r, [x; y]))];
    [enot (eapp ("=", [z; t])); enot (eapp (r, [z; t]))];
  |] in
  {
    nconc = [e1; e2];
    nrule = if sym then Trans_sym (e1, e2) else Trans (e1, e2);
    nprio = Arity;
    nbranches = branches;
  }
;;

let mknode_negtrans sym e2 e1 = mknode_trans sym e1 e2;;

let mknode_transeq sym e1 e2 =
  let (r, a, b, c, d) =
    match e1, e2 with
    | Eapp ("=", [a; b], _), Enot (Eapp (r, [c; d], _), _) -> (r, a, b, c, d)
    | _, _ -> assert false
  in
  let (x, y, z, t) = if sym then (d, a, b, c) else (c, a, b, d) in
  let branches = [|
    [enot (eapp ("=", [x; y])); enot (eapp (r, [x; y]))];
    [enot (eapp (r, [x; y])); enot (eapp (r, [z; t]))];
    [enot (eapp ("=", [z; t])); enot (eapp (r, [z; t]))];
  |] in
  {
    nconc = [e1; e2];
    nrule = if sym then TransEq_sym (a, b, e2) else TransEq (a, b, e2);
    nprio = Arity;
    nbranches = branches;
  }
;;

let mknode_negtranseq sym e2 e1 = mknode_transeq sym e1 e2;;

let get_rhs e =
  match e with
  | Eapp (_, [f1; f2], _) -> f2
  | _ -> assert false
;;

let get_lhs e =
  match e with
  | Eapp (_, [f1; f2], _) -> f1
  | _ -> assert false
;;

let newnodes_match_trans st fm =
  match fm with
  | Eapp ("=", [Emeta (m1, _); Emeta (m2, _)], _) ->
      if m2 > m1 then begin
        Index.add_trans fm Index.Left;
        let matches_ll = Index.find_all_negtrans () in
        let matches_rl = matches_ll in
        let nodes = List.flatten [
          List.map (mknode_transeq false fm) matches_ll;
          List.map (mknode_transeq true fm) matches_rl;
        ] in
        let st1 = add_node_list st nodes in
        let crit_r = Index.find_all_trans_rightonly Index.Wild in
        let crit_l = Index.find_all_trans_leftonly Index.Wild in
        let pairs = (List.map get_lhs crit_l) @@ (List.map get_rhs crit_r) in
        let f (st, _) e = make_inst st m1 e in
        let (st2, _) = List.fold_left f (st1, true) pairs in
        (st2, true)
      end else begin
        Index.add_trans fm Index.Right;
        let matches_rr = Index.find_all_negtrans () in
        let matches_lr = matches_rr in
        let nodes = List.flatten [
          List.map (mknode_trans false fm) matches_rr;
          List.map (mknode_trans true fm) matches_lr;
        ] in
        let st1 = add_node_list st nodes in
        let crit_l = Index.find_all_trans_leftonly Index.Wild in
        let crit_r = Index.find_all_trans_rightonly Index.Wild in
        let pairs = (List.map get_rhs crit_r) @@ (List.map get_lhs crit_l) in
        let f (st, _) e = make_inst st m2 e in
        let (st2, _) = List.fold_left f (st1, true) pairs in
        (st2, true)
      end
  | Eapp (s, [Emeta (m1, _); Emeta (m2, _)], _) when Eqrel.trans s ->
      if m2 > m1 then begin
        Index.add_trans fm Index.Left;
        let matches_ll = Index.find_neg s in
        let matches_rl = if Eqrel.sym s then matches_ll else [] in
        let nodes = List.flatten [
          List.map (mknode_trans false fm) matches_ll;
          List.map (mknode_trans true fm) matches_rl;
        ] in
        let st1 = add_node_list st nodes in
        let crit_r = Index.find_trans_rightonly s Index.Wild in
        let crit_l =
          if Eqrel.sym s then Index.find_trans_leftonly s Index.Wild else []
        in
        let pairs = (List.map get_lhs crit_l) @@ (List.map get_rhs crit_r) in
        let f (st, _) e = make_inst st m1 e in
        let (st2, _) = List.fold_left f (st1, true) pairs in
        (st2, true)
      end else begin
        Index.add_trans fm Index.Right;
        let matches_rr = Index.find_neg s in
        let matches_lr = if Eqrel.sym s then matches_rr else [] in
        let nodes = List.flatten [
          List.map (mknode_trans false fm) matches_rr;
          List.map (mknode_trans true fm) matches_lr;
        ] in
        let st1 = add_node_list st nodes in
        let crit_l = Index.find_trans_leftonly s Index.Wild in
        let crit_r =
          if Eqrel.sym s then Index.find_trans_rightonly s Index.Wild else []
        in
        let pairs = (List.map get_rhs crit_r) @@ (List.map get_lhs crit_l) in
        let f (st, _) e = make_inst st m2 e in
        let (st2, _) = List.fold_left f (st1, true) pairs in
        (st2, true)
      end
  | Eapp ("=", [Emeta _; e2], _) ->
      Index.add_trans fm Index.Right;
      let h2 = Index.get_head e2 in
      let matches_rr = Index.find_all_negtrans_right h2 in
      let matches_lr = Index.find_all_negtrans_left h2 in
      let nodes = List.flatten [
        List.map (mknode_transeq false fm) matches_rr;
        List.map (mknode_transeq true fm) matches_lr;
      ] in
      let st1 = add_node_list st nodes in
      let crit_l = Index.find_all_trans_leftonly h2 in
      let crit_r = Index.find_all_trans_rightonly h2 in
      let pairs_l = List.map (fun e -> preunify e2 (get_lhs e)) crit_l in
      let pairs_r = List.map (fun e -> preunify e2 (get_rhs e)) crit_r in
      let pairs = List.flatten (pairs_r @@ pairs_l) in
      let f (st, _) (m, e) = make_inst st m e in
      let (st2, _) = List.fold_left f (st1, true) pairs in
      (st2, true)
  | Eapp (s, [Emeta _; e2], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Right;
      let h2 = Index.get_head e2 in
      let matches_rr = Index.find_negtrans_right s h2 in
      let matches_lr =
        if Eqrel.sym s then Index.find_negtrans_left s h2 else []
      in
      let nodes = List.flatten [
        List.map (mknode_trans false fm) matches_rr;
        List.map (mknode_trans true fm) matches_lr;
      ] in
      let st1 = add_node_list st nodes in
      let crit_l = Index.find_trans_leftonly s h2 in
      let crit_r = if Eqrel.sym s then Index.find_trans_rightonly s h2 else []
      in
      let pairs_l = List.map (fun e -> preunify e2 (get_lhs e)) crit_l in
      let pairs_r = List.map (fun e -> preunify e2 (get_rhs e)) crit_r in
      let pairs = List.flatten (pairs_r @@ pairs_l) in
      let f (st, _) (m, e) = make_inst st m e in
      let (st2, _) = List.fold_left f (st1, true) pairs in
      (st2, true)
  | Eapp ("=", [e1; Emeta _], _) ->
      Index.add_trans fm Index.Left;
      let h1 = Index.get_head e1 in
      let matches_ll = Index.find_all_negtrans_left h1 in
      let matches_rl = Index.find_all_negtrans_right h1 in
      let nodes = List.flatten [
        List.map (mknode_transeq false fm) matches_ll;
        List.map (mknode_transeq true fm) matches_rl;
      ] in
      let st1 = add_node_list st nodes in
      let crit_r = Index.find_all_trans_rightonly h1 in
      let crit_l = Index.find_all_trans_leftonly h1 in
      let pairs_r = List.map (fun e -> preunify e1 (get_rhs e)) crit_r in
      let pairs_l = List.map (fun e -> preunify e1 (get_lhs e)) crit_l in
      let pairs = List.flatten (pairs_l @@ pairs_r) in
      let f (st, _) (m, e) = make_inst st m e in
      let (st2, _) = List.fold_left f (st1, true) pairs in
      (st2, true)
  | Eapp (s, [e1; Emeta _], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Left;
      let h1 = Index.get_head e1 in
      let matches_ll = Index.find_negtrans_left s h1 in
      let matches_rl =
        if Eqrel.sym s then Index.find_negtrans_right s h1 else []
      in
      let nodes = List.flatten [
        List.map (mknode_trans false fm) matches_ll;
        List.map (mknode_trans true fm) matches_rl;
      ] in
      let st1 = add_node_list st nodes in
      let crit_r = Index.find_trans_rightonly s h1 in
      let crit_l = if Eqrel.sym s then Index.find_trans_leftonly s h1 else [] in
      let pairs_r = List.map (fun e -> preunify e1 (get_rhs e)) crit_r in
      let pairs_l = List.map (fun e -> preunify e1 (get_lhs e)) crit_l in
      let pairs = List.flatten (pairs_l @@ pairs_r) in
      let f (st, _) (m, e) = make_inst st m e in
      let (st2, _) = List.fold_left f (st1, true) pairs in
      (st2, true)
  | Eapp ("=", [e1; e2], _) ->
      Index.add_trans fm Index.Both;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = Index.find_all_negtrans_left h1 in
      let matches_rr = Index.find_all_negtrans_right h2 in
      let matches_lr = Index.find_all_negtrans_left h2 in
      let matches_rl = Index.find_all_negtrans_right h1 in
      let nodes = List.flatten [
        List.map (mknode_transeq false fm) matches_ll;
        List.map (mknode_transeq true fm) matches_lr;
        List.map (mknode_transeq true fm) matches_rl;
        List.map (mknode_transeq false fm) matches_rr;
      ] in
      add_node_list st nodes, true
  | Eapp (s, [e1; e2], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Both;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = Index.find_negtrans_left s h1 in
      let matches_rr = Index.find_negtrans_right s h2 in
      let matches_lr = if Eqrel.sym s then Index.find_negtrans_left s h2 else []
      in
      let matches_rl =
        if Eqrel.sym s then Index.find_negtrans_right s h1 else []
      in
      let nodes = List.flatten [
        List.map (mknode_trans false fm) matches_ll;
        List.map (mknode_trans true fm) matches_lr;
        List.map (mknode_trans true fm) matches_rl;
        List.map (mknode_trans false fm) matches_rr;
      ] in
      add_node_list st nodes, true
  | Enot (Eapp (s, [e1; e2], _), _) when Eqrel.trans s ->
      Index.add_negtrans fm;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = Index.find_trans_left s h1 in
      let matches_rr = Index.find_trans_right s h2 in
      let matches_lr = if Eqrel.sym s then Index.find_trans_right s h1 else []
      in
      let matches_rl = if Eqrel.sym s then Index.find_trans_left s h2 else []
      in
      let nodes = List.flatten [
        List.map (mknode_negtrans false fm) matches_ll;
        List.map (mknode_negtrans true fm) matches_lr;
        List.map (mknode_negtrans true fm) matches_rl;
        List.map (mknode_negtrans false fm) matches_rr;
      ] in
      let eqnodes =
        if s =%= "=" then [] else
        let eqmatches_ll = Index.find_trans_left "=" h1 in
        let eqmatches_rr = Index.find_trans_right "=" h2 in
        let eqmatches_lr =
          if Eqrel.sym s then Index.find_trans_right "=" h1 else []
        in
        let eqmatches_rl =
          if Eqrel.sym s then Index.find_trans_left "=" h2 else []
        in
        List.flatten [
          List.map (mknode_negtranseq false fm) eqmatches_ll;
          List.map (mknode_negtranseq true fm) eqmatches_lr;
          List.map (mknode_negtranseq true fm) eqmatches_rl;
          List.map (mknode_negtranseq false fm) eqmatches_rr;
        ]
      in
      add_node_list st (eqnodes @@ nodes), true
  | _ -> st, false
;;

let newnodes_match_sym st fm =
  match fm with
  | Enot (Eapp (s, [a1; a2], _), _) when Eqrel.sym s ->
      let do_match st p = make_notequiv st true p fm in
      List.fold_left do_match st (Index.find_pos s), false
  | Eapp (s, [a1; a2], _) when Eqrel.sym s ->
      let do_match st p = make_notequiv st true fm p in
      List.fold_left do_match st (Index.find_neg s), false
  | _ -> (st, false)
;;

let newnodes_match st fm =
  match fm with
  | Enot (Eapp (s, _, _), _) ->
      let do_match st p = make_notequiv st false p fm in
      List.fold_left do_match st (Index.find_pos s), true
  | Eapp (s, _, _) ->
      let do_match st p = make_notequiv st false fm p in
      List.fold_left do_match st (Index.find_neg s), true
  | _ -> (st, false)
;;

let newnodes_preunif st fm =
  match fm with
  | Enot (Eapp (s, _, _), _) ->
      let do_match st p =
        let f st1 (m, e) = fst (make_inst st1 m e) in
        List.fold_left f st (preunify p fm)
      in
      List.fold_left do_match st (Index.find_pos s), false
  | Eapp (s, _, _) ->
      let do_match st p =
        let f st1 (m, e) = fst (make_inst st1 m e) in
        List.fold_left f st (preunify p fm)
      in
      List.fold_left do_match st (Index.find_neg s), false
  | _ -> (st, false)
;;

let newnodes_useless st fm =
  match fm with
  | Evar (v, _)
  | Enot (Evar (v, _), _)
    -> st, true

  | Etrue | Enot (Efalse, _)
    -> st, true

  | Emeta _ | Etau _ | Elam _ | Enot ((Emeta _ | Etau _ | Elam _), _)
    ->
      if !Globals.warnings_flag then begin
        fprintf stderr "add_nodes: unexpected formula meta/tau";
        Print.expr (Print.Chan stderr) fm;
        printf "\n";
      end;
      st, true
  | _ -> (st, false)
;;

(* TODO permettre aux extensions de modifier l'etat ? *)

let add_nodes st fm =
  let combine (state, stop) f =
    if stop then (state, true) else f state fm
  in
  let (st1, stop1) =
    List.fold_left combine (st, false) [
      newnodes_absurd;
      newnodes_closure;
    ]
  in
  let (newnodes2, stop2) = Node.relevant (Extension.newnodes fm) in
  let insert_node s n = {s with queue = insert s.queue n} in
  let st2 = List.fold_left insert_node st1 newnodes2 in
  let (st3, stop3) =
    List.fold_left combine (st2, stop2) [
      newnodes_jtree;
      newnodes_alpha;
      newnodes_beta;
      newnodes_delta;
      newnodes_gamma;
      newnodes_unfold;
      newnodes_refl;
      newnodes_preunif;
      newnodes_match_congruence;
      newnodes_match_trans;
      newnodes_match_sym;
      newnodes_match;
      newnodes_useless;
    ]
  in
  st3
;;

let rec reduce_list accu l =
  match l with
  | [] -> accu
  | Enot (Efalse, _) :: t -> reduce_list accu t
  | Eapp (s, [e1; e2], _) :: t when Expr.equal e1 e2 && Eqrel.refl s ->
      reduce_list accu t
  | Eapp (s, [e1; e2], _) as f :: t when Eqrel.sym s ->
      let g = eapp (s, [e2; e1]) in
      if Index.member f || Index.member g
         || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
      then reduce_list accu t
      else reduce_list (f :: accu) t
  | Enot (Eapp (s, [e1; e2], _), _) as f :: t when Eqrel.sym s ->
     let g = enot (eapp (s, [e2; e1])) in
     if Index.member f || Index.member g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | f :: t ->
     if Index.member f || List.exists (Expr.equal f) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
;;

let reduce_branches n =
  let reduced = Array.map (reduce_list []) n.nbranches in
  let rec array_exists f a i =
    if i >= Array.length a then false
    else if f a.(i) then true
    else array_exists f a (i+1)
  in
  if array_exists (function [] -> true | _ -> false) reduced 0
  then None
  else Some { n with nbranches = reduced }
;;

let sort_uniq l =
  let l1 = List.sort Pervasives.compare l in
  let rec uniq l accu =
    match l with
    | [] | [_] -> l @ accu
    | x :: (y :: _ as t) when x =%= y -> uniq t accu
    | x :: t -> uniq t (x :: accu)
  in
  uniq l1 []
;;

let count_meta_list l =
  List.length (sort_uniq (List.flatten (List.map get_metas l)))
;;

let find_open_branch node brstate =
  let last = Array.length brstate - 1 in
  if brstate =%= [| |] then None
  else if brstate.(last) =%= Open then Some last else begin
    let rec loop accu i =
      if i < 0 then accu
      else if brstate.(i) =%= Open then loop (i::accu) (i-1)
      else loop accu (i-1)
    in
    let open_branches = loop [] last in
    match open_branches with
    | [] -> None
    | [i] -> Some i
    | l ->
        let score i =
          let fs = node.nbranches.(i) in
          let f accu x = accu + Expr.size x in
          let s = List.fold_left f 0 fs in
          (count_meta_list fs, s, i)
        in
        let l1 = List.map score l in
        let cmp (len1, size1, _) (len2, size2, _) =
          if len1 =%= len2
          then size1 - size2
(* FIXME mieux ? pire ? pareil ?
          then if len1 =%= 0 then size1 - size2 else size2 - size1
*)
          else len2 - len1
        in
        let l2 = List.sort cmp l1 in
        begin match l2 with
        | (_, _, i) :: _ -> Some i
        | _ -> assert false
        end
  end
;;

let dummy_proof = {
  mlconc = [];
  mlrule = False;
  mlhyps = [| |];
  mlrefc = 0;
};;

let is_equiv r =
  match r with
  | Equiv _ | NotEquiv _ -> true
  | _ -> false
;;

let add_virtual_branch n =
  let len = Array.length n.nbranches in
  if len < 2 then begin
    (n, Array.make len Open)
  end else begin
    let branches = Array.make (len+1) [] in
    let brstate = Array.make (len+1) Open in
    for i = 0 to len - 1 do
      branches.(i) <- n.nbranches.(i);
      let has_metas fm = Expr.count_metas fm > 0 in
      let with_metas = List.filter has_metas n.nbranches.(i) in
      branches.(len) <- with_metas @@ branches.(len);
    done;

    if List.length branches.(len) < 2 || is_equiv n.nrule then begin
      brstate.(len) <- Closed dummy_proof;
    end;
    ({n with nbranches = branches}, brstate)
  end
;;

let remove_virtual_branch n brst =
  let len = Array.length n.nbranches in
  if len < 2 then begin
    (n, brst)
  end else begin
    let branches = Array.sub n.nbranches 0 (len-1) in
    let brstate = Array.sub brst 0 (len-1) in
    ({n with nbranches = branches}, brstate)
  end
;;

let good_lemma rule =
  match rule with
  | Close _ | Close_refl _ | Close_sym _ | False | NotTrue -> false
  | _ -> true
;;

(* there is no [Open] in [branches]; make a proof node *)
let make_result n nbranches =
  let concs = ref []
  and proofs = ref []
  in
  for i = 0 to Array.length nbranches - 1 do
    match nbranches.(i) with
    | Open -> assert false
    | Closed p ->
        proofs := p :: !proofs;
        concs := union (diff p.mlconc n.nbranches.(i)) !concs;
  done;
  assert (List.length !proofs == Array.length n.nbranches);
  let prf_node = {
    mlconc = union n.nconc !concs;
    mlrule = n.nrule;
    mlhyps = Array.of_list (List.rev !proofs);
    mlrefc = 1;
  } in
  incr Globals.proof_nodes;
  if good_lemma n.nrule then begin
    Index.add_proof prf_node;
  end;
  Closed prf_node
;;

let good_head q =
  match head q with
  | None -> true
  | Some node -> good_lemma node.nrule
;;

exception NoProof;;

let progress_period = ref 100;;
let progress_counter = ref !progress_period;;
let progress_last = ref 0.0;;
let period_base = 0.3;;

let check_limits () =
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let tm = Sys.time () in
  if tm > !progress_last +. 0.001 then begin
    let new_period = float !progress_period *. period_base
                     /. (tm -. !progress_last) in
    progress_period := int_of_float new_period;
  end;
  if !progress_period < 1 then progress_period := 1;
  progress_last := tm;
  if tm > !Globals.time_limit then begin
    eprintf " time out\n";
    flush stderr;
    raise NoProof;
  end;
  if float heap_size > !Globals.size_limit then begin
    eprintf " size out\n";
    flush stderr;
    raise NoProof;
  end;
;;

let rec refute_aux stk st forms =
  match forms with
  | [] ->
(*
eprintf "queue sizes = %s\n" (Node.size st.queue); flush stderr;
*)
      if good_head st.queue then begin
        match Index.search_proof () with
        | Some p -> p.mlrefc <- p.mlrefc + 1; unwind stk (Closed p)
        | None -> next_node stk st
      end else begin
        next_node stk st
      end
  | Eapp (s, [e1; e2], _) :: fms when Eqrel.refl s && Expr.equal e1 e2 ->
      refute_aux stk st fms
  | fm :: fms ->
      Index.add fm 0;
      Extension.add_formula fm;
      refute_aux stk (add_nodes st fm) fms

and refute stk st forms =
  Step.forms "refute" forms;
  decr progress_counter;
  if !progress_counter < 0 then begin
    check_limits ();
    progress_counter := !progress_period;
    Progress.do_progress (fun () -> ());
  end;
  refute_aux stk st forms

and next_node stk st =
  incr Globals.inferences;
  match remove st.queue with
  | None ->
      if !Globals.debug_flag then Step.forms "NO PROOF" (Index.get_all ());
      raise NoProof
  | Some (n, q1) ->
      let st1 = {st with queue = q1} in
      match reduce_branches n with
      | Some n1 ->
          let (n2, brstate) = add_virtual_branch n1 in
          next_branch stk n2 st1 brstate
      | None -> next_node stk st1

and next_branch stk n st brstate =
  Step.rule "next_branch" n.nrule;
  match find_open_branch n brstate with
  | Some i ->
      let fr = {node = n; state = st; brst = brstate; curbr = i} in
      incr cur_depth;
      if !cur_depth > !top_depth then top_depth := !cur_depth;
      refute (fr :: stk) st n.nbranches.(i)
  | None ->
      let (n1, brstate1) = remove_virtual_branch n brstate in
      let result = make_result n1 brstate1 in
      unwind stk result

and unwind stk res =
  match stk with
  | [] -> res
  | fr :: stk1 ->
      Step.rule "unwind" fr.node.nrule;
      let f x =
        if Index.member x then begin (* we can unwind before adding all forms *)
          Extension.remove_formula x;
          Index.remove x;
        end;
      in
      List.iter f (List.rev fr.node.nbranches.(fr.curbr));
      decr cur_depth;
      begin match res with
      | Closed p when disjoint fr.node.nbranches.(fr.curbr) p.mlconc ->
          unwind stk1 res
      | Closed _ ->
          fr.brst.(fr.curbr) <- res;
          next_branch stk1 fr.node fr.state fr.brst
      | Open -> assert false
      end;
;;

let rec reduce_initial_list accu l =
  match l with
  | [] -> accu
  | (f, p) as fp :: t ->
      if List.exists (fun (e, _) -> Expr.equal f e) accu
      then reduce_initial_list accu t
      else reduce_initial_list (fp :: accu) t
;;

let ticker finished () =
  let tm = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  Progress.do_progress begin fun () ->
    eprintf "depth %5d/%d  search %d  proof %d  \
             lemma %d  size %dM  time %.0f\n"
            !cur_depth !top_depth !Globals.inferences !Globals.proof_nodes
            !Globals.stored_lemmas (heap_size / 1_000_000) tm;
  end;
  if not finished then check_limits ();
;;

let rm_goalness l = List.map fst l;;

let prove defs l =
  try
    List.iter Index.add_def defs;
    let al = Gc.create_alarm (ticker false) in
    let rl = reduce_initial_list [] l in
    let wl = rm_goalness rl in
    Globals.inferences := 0;
    Globals.proof_nodes := 0;
    cur_depth := 0;
    top_depth := 0;
    let result = refute [] {queue = empty; inst = IntMap.empty} wl in
    Gc.delete_alarm al;
    ticker true ();
    Progress.end_progress "";
    match result with
    | Closed p -> p
    | Open -> assert false
  with NoProof ->
    Progress.end_progress " search failed";
    raise NoProof
;;
