(*  Copyright 2002 INRIA  *)
Version.add "$Id: prove.ml,v 1.8 2004-09-09 15:25:35 doligez Exp $";;

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;

let _equal = ( = );;
let ( = ) = ();;
let string_equal x y = String.compare x y == 0;;

type branch_state =
  | Open
  | Closed of proof
  | Back of expr list  (* formulas that caused the backtrack *)
;;

type snode = {
  sconc : expr list;
  srule : rule;
  sprio : Prio.t;
  sgoalness : int;
  sbranches : expr list array;
  snobacktrack : bool;
};;

type frame = {
  node : snode;
  queue : snode Heap.t;
  state : branch_state array;
  cur : int;
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
  | Eall (v, t, f, _) -> eall (v, t, replace_meta m va f)
  | Eex (v, t, f, _) -> eex (v, t, replace_meta m va f)
  | Etau (v, t, f, _) -> etau (v, t, replace_meta m va f)
;;

let rec pure_meta l =
  let is_meta = function
    | Emeta _ -> true
    | _ -> false
  in
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

let average_goalness l =
  let total = List.fold_left (fun acc e -> acc + Index.get_goalness e) 0 l in
  total / List.length l
;;

let add_back noback n = {
  sconc = n.nconc;
  srule = n.nrule;
  sprio = n.nprio;
  sgoalness = average_goalness n.nconc;
  sbranches = n.nbranches;
  snobacktrack =
    begin match n.nrule with
      | All _ | NotEx _ -> true
      | _ -> noback
    end;
};;

(****************)

let rec occurs_under_tau e1 e2 =
  match e2 with
  | Evar _ | Emeta _ | Etrue | Efalse -> false
  | Eapp (_, args, _) -> List.exists (occurs_under_tau e1) args
  | Eand (f, g, _) | Eor (f, g, _) | Eimply (f, g, _) | Eequiv (f, g, _)
    -> occurs_under_tau e1 f || occurs_under_tau e1 g
  | Enot (f, _) | Eall (_, _, f, _) | Eex (_, _, f, _) -> occurs_under_tau e1 f
  | Etau (_, _, f, _) -> Expr.occurs e1 f
;;

(* [make_inst m e prio extra_weight]
   create the node that instantiates m with e,
*)
let make_inst m e =
  let mm = emeta m in
  if Expr.occurs mm e then begin
    if occurs_under_tau mm e then [] else
    match m with
    | Eall (v, t, p, _) ->
        let f = replace_meta mm v e in
        let n = eall (v, t, Expr.substitute [(v, f)] p) in
        let branches = [| [n] |] in
        [ Node {
          nconc = [m];
          nrule = AllPartial (m, n);
          nprio = Prio.make !cur_depth (Prio.Gamma_inst e) branches;
          nbranches = branches;
        } ]
    | Enot (Eex (v, t, p, _), _) ->
        let f = replace_meta mm v e in
        let n = enot (eex (v, t, Expr.substitute [(v, f)] p)) in
        let branches = [| [n] |] in
        [ Node {
          nconc = [m];
          nrule = NotExPartial (m, n);
          nprio = Prio.make !cur_depth (Prio.Gamma_inst e) branches;
          nbranches = branches;
        } ]
    | _ -> assert false
  end else begin
    match m with
    | Eall (v, t, p, _) ->
        let branches = [| [Expr.substitute [(v, e)] p] |] in
        [ Node {
          nconc = [m];
          nrule = All (m, e);
          nprio = Prio.make !cur_depth (Prio.Gamma_inst e) branches;
          nbranches = branches;
        } ]
    | Enot (Eex (v, t, p, _), _) ->
        let branches = [| [enot (Expr.substitute [(v, e)] p)] |] in
        [ Node {
          nconc = [m];
          nrule = NotEx (m, e);
          nprio = Prio.make !cur_depth (Prio.Gamma_inst e) branches;
          nbranches = branches;
        } ]
    | _ -> assert false
  end
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
  if !Globals.warnings_flag then begin
    eprintf "Warning: symbol %s is used with inconsistent arities\n" s;
    flush stderr;
  end;
;;

let make_notequiv sym p np =
  match p, np with
  | Eapp (s1, args1, _), Enot (Eapp (s2, args2, _), _) ->
      assert (string_equal s1 s2);
      if sym && List.length args2 != 2
         || List.length args1 <> List.length args2
      then (arity_warning s1; [])
      else
        let myrule = if sym then P_NotP_sym (s1, p, np) else P_NotP (p, np) in
        let myargs1 = if sym then List.rev args1 else args1 in
        let branches = make_inequals myargs1 args2 in
        [ Node {
          nconc = [p; np];
          nrule = myrule;
          nprio = Prio.make !cur_depth Prio.Correl branches;
          nbranches = branches;
        } ]
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

let newnodes_absurd fm =
  match fm with
  | Enot (p, _) when Index.member p -> [ Node {
      nconc = [fm; p];
      nrule = Close (p);
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | p when Index.member (enot p) -> [ Node {
      nconc = [p; enot p];
      nrule = Close (p);
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | _ -> []
;;

let newnodes_closure fm =
  match fm with
  | Efalse -> [ Node {
      nconc = [fm];
      nrule = False;
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | Enot (Etrue, _) -> [ Node {
      nconc = [fm];
      nrule = NotTrue;
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | Enot (Eapp (s, [a; b], _), _) when Eqrel.refl s && Expr.equal a b ->
    [ Node {
      nconc = [fm];
      nrule = Close_refl (s, a);
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | Eapp (s, [e1; e2], _)
    when Eqrel.sym s && Index.member (enot (eapp (s, [e2; e1]))) ->
    [ Node {
      nconc = [fm; (enot (eapp (s, [e2; e1])))];
      nrule = Close_sym (s, e1, e2);
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | Enot (Eapp (s, [e1; e2], _), _)
    when Eqrel.sym s && Index.member (eapp (s, [e2; e1])) ->
    [ Node {
      nconc = [fm; (eapp (s, [e2; e1]))];
      nrule = Close_sym (s, e2, e1);
      nprio = Prio.make !cur_depth Prio.Close [| |];
      nbranches = [| |];
    }; Stop ]
  | _ -> []
;;

let newnodes_jtree fm =
  match fm with
  | Eand _ | Enot (Eor _, _) | Enot (Eimply _, _)
    when is_conj fm 3 == 0 ->
      let branches = [| decomp_conj false [] fm |] in
      [ Node {
        nconc = [fm];
        nrule = ConjTree fm;
        nprio = Prio.make !cur_depth Prio.Alpha2 branches;
        nbranches = branches;
      }; Stop ]
  | Eor _ | Enot (Eand _, _) | Eimply _
    when is_disj fm 3 == 0 ->
      let forms = Array.of_list (decomp_disj false [] fm) in
      let branches = Array.map (fun x -> [x]) forms in
      [ Node {
        nconc = [fm];
        nrule = DisjTree fm;
        nprio = Prio.make !cur_depth Prio.Beta1 branches;
        nbranches = branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_alpha fm =
  match fm with
  | Enot (Enot (a, _), _) ->
      let branches = [| [a] |] in
      [ Node {
        nconc = [fm];
        nrule = NotNot (a);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eand (a, b, _) ->
      let branches = [| [a; b] |] in
      [ Node {
        nconc = [fm];
        nrule = And (a, b);
        nprio = Prio.make !cur_depth Prio.Alpha2 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eor (a, b, _), _) ->
      let branches = [| [enot (a); enot (b)] |] in
      [ Node {
        nconc = [fm];
        nrule = NotOr (a, b);
        nprio = Prio.make !cur_depth Prio.Alpha2 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eimply (a, b, _), _) ->
      let branches = [| [a; enot (b)] |] in
      [ Node {
        nconc = [fm];
        nrule = NotImpl (a, b);
        nprio = Prio.make !cur_depth Prio.Beta1 branches;
        nbranches = branches
      }; Stop ]
  | _ -> []
;;

let newnodes_beta fm =
  match fm with
  | Eor (a, b, _) ->
      let branches = [| [a]; [b] |] in
      [ Node {
        nconc = [fm];
        nrule = Or (a, b);
        nprio = Prio.make !cur_depth Prio.Beta1 branches;
        nbranches = branches;
      }; Stop ]
  | Eimply (a, b, _) ->
      let branches = [| [enot (a)]; [b] |] in
      [ Node {
        nconc = [fm];
        nrule = Impl (a, b);
        nprio = Prio.make !cur_depth Prio.Beta1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eand (a, b, _), _) ->
      let branches = [| [enot (a)]; [enot (b)] |] in
      [ Node {
        nconc = [fm];
        nrule = NotAnd (a, b);
        nprio = Prio.make !cur_depth Prio.Beta1 branches;
        nbranches = branches;
      }; Stop ]
  | Eequiv (a, b, _) ->
      let branches = [| [enot (a); enot (b)]; [a; b] |] in
      [ Node {
        nconc = [fm];
        nrule = Equiv (a, b);
        nprio = Prio.make !cur_depth Prio.Beta2 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eequiv (a, b, _), _) ->
      let branches = [| [enot (a); b]; [a; enot (b)] |] in
      [ Node {
        nconc = [fm];
        nrule = NotEquiv (a, b);
        nprio = Prio.make !cur_depth Prio.Beta2 branches;
        nbranches = branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_delta fm =
  match fm with
  | Eex (v, t, p, _) ->
      let branches = [| [Expr.substitute [(v, etau (v, t, p))] p] |] in
      [ Node {
        nconc = [fm];
        nrule = Ex (fm);
        nprio = Prio.make !cur_depth Prio.Delta branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eall (v, t, p, _), _) ->
      let np = enot (p) in
      let branches = [| [Expr.substitute [(v, etau (v, t, np))] np] |] in
      [ Node {
        nconc = [fm];
        nrule = NotAll (fm);
        nprio = Prio.make !cur_depth Prio.Delta branches;
        nbranches = branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_gamma fm =
  match fm with
  | Eall (v, t, p, _) ->
      let w = emeta (fm) in
      let branches = [| [Expr.substitute [(v, w)] p] |] in
      [ Node {
        nconc = [fm];
        nrule = All (fm, w);
        nprio = Prio.make !cur_depth Prio.Gamma_meta branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eex (v, t, p, _), _) ->
      let w = emeta (fm) in
      let branches = [| [enot (Expr.substitute [(v, w)] p)] |] in
      [ Node {
        nconc = [fm];
        nrule = NotEx (fm, w);
        nprio = Prio.make !cur_depth Prio.Gamma_meta branches;
        nbranches = branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_unfold fm =
  match fm with
  | Eapp (p, args, _) when Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = substitute subst body in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end
  | Enot (Eapp (p, args, _), _) when Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (substitute subst body) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end
  | Eapp (s, [Eapp (p, args, _); e], _) when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp (s, [substitute subst body; e]) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end
  | Eapp (s, [e; Eapp (p, args, _)], _) when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = eapp (s, [e; substitute subst body]) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end
  | Enot (Eapp (s, [Eapp (p, args, _); e], _), _)
    when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp (s, [substitute subst body; e])) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end
  | Enot (Eapp (s, [e; Eapp (p, args, _)], _), _)
    when Eqrel.any s && Index.has_def p ->
      begin try
        let (d, params, body) = Index.get_def p in
        let subst = List.map2 (fun x y -> (x,y)) params args in
        let unfolded = enot (eapp (s, [e; substitute subst body])) in
        let branches = [| [unfolded] |] in
        [ Node {
            nconc = [fm];
            nrule = Definition (d, fm, unfolded);
            nprio = Prio.make !cur_depth Prio.Alpha1 branches;
            nbranches = branches;
        }; Stop ]
      with
      | Invalid_argument "List.map2" -> arity_warning p; []
      | Not_found -> assert false
      end

  | Evar (v, _) when Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let branches = [| [body] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, body);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Evar (v, _), _) when Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot body in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, unfolded);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp (s, [Evar (v, _); e], _) when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = eapp (s, [body; e]) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, unfolded);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Eapp (s, [e; Evar (v, _)], _) when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = eapp (s, [e; body]) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, unfolded);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp (s, [Evar (v, _); e], _), _)
    when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot (eapp (s, [body; e])) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, unfolded);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | Enot (Eapp (s, [e; Evar (v, _)], _), _)
    when Eqrel.any s && Index.has_def v ->
      let (d, params, body) = Index.get_def v in
      let unfolded = enot (eapp (s, [e; body])) in
      let branches = [| [unfolded] |] in
      if params <> [] then (arity_warning v; [])
      else [ Node {
        nconc = [fm];
        nrule = Definition (d, fm, unfolded);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_refl fm =
  match fm with
  | Enot (Eapp (s, [e1; e2], _), _) when s <> "=" && Eqrel.refl s ->
      let branches = [| [enot (eapp ("=", [e1; e2]))] |] in
      [ Node {
        nconc = [fm];
        nrule = Refl (s, e1, e2);
        nprio = Prio.make !cur_depth Prio.Alpha1 branches;
        nbranches = branches;
      } ]

  | Enot (Eapp ("=", [(Emeta (m1, _) as mm1); (Emeta (m2, _) as mm2)], _), _)
    ->
      let d1 = Index.get_meta m1 and d2 = Index.get_meta m2 in
      if d1 < d2
      then make_inst m2 mm1 @ [Stop]
      else make_inst m1 mm2 @ [Stop]

  | Enot (Eapp ("=", [Emeta (m, _); e], _), _) -> make_inst m e @ [Stop]
  | Enot (Eapp ("=", [e; Emeta (m, _)], _), _) -> make_inst m e @ [Stop]

  | _ -> []
;;

let newnodes_match_congruence fm =
  match fm with
  | Enot (Eapp ("=", [(Eapp (f1, a1, _) as e1);
                      (Eapp (f2, a2, _) as e2)], _), _)
    when string_equal f1 f2 ->
      if List.length a1 == List.length a2 then begin
        let branches = make_inequals a1 a2 in
        [ Node {
          nconc = [fm];
          nrule = NotEqual (e1, e2);
          nprio = Prio.make !cur_depth Prio.Beta2 branches;
          nbranches = branches;
        } ]
      end else (arity_warning f1; [])
  | _ -> []
;;

let mknode_trans s1 s2 e1 e2 =
  let (s, a, b, c, d) =
    match e1, e2 with
    | Enot (Eapp (s, [a; b], _), _), Eapp (_, [c; d], _) -> (s, a, b, c, d)
    | _, _ -> assert false
  in
  let side, sym, x, y, z, t =
    match s1, s2 with
    | L, L -> (L, false, c, a, d, b)
    | R, R -> (R, false, d, b, a, c)
    | R, L -> (L, true, c, b, a, d)
    | L, R -> (R, true, d, a, c, b)
  in
  let branches = [| [enot (eapp ("=", [x; y]))]; [enot (eapp (s, [z; t]))] |] in
  Node {
    nconc = [e1; e2];
    nrule = Trans (side, sym, e1, e2);
    nprio = Prio.make !cur_depth Prio.Correl branches;
    nbranches = branches;
  }
;;

let mknode_negtrans s1 s2 e2 e1 = mknode_trans s1 s2 e1 e2;;

let find_trans_left s h =
  (if string_equal s "=" then [] else Index.find_trans_left s h)
  @@ Index.find_trans_left "=" h
;;

let find_trans_right s h =
  (if string_equal s "=" then [] else Index.find_trans_right s h)
  @@ Index.find_trans_right "=" h
;;

let find_negtrans_left s h =
  if string_equal s "="
  then Index.find_all_negtrans_left h
  else Index.find_negtrans_left s h
;;

let find_negtrans_right s h =
  if string_equal s "="
  then Index.find_all_negtrans_right h
  else Index.find_negtrans_right s h
;;

let newnodes_match_trans fm =
  match fm with
  | Eapp (s, [(Emeta (m1, _) as mm1); (Emeta (m2, _) as mm2)], _)
    when Eqrel.trans s ->
      if Index.get_meta m1 < Index.get_meta m2 then begin
        Index.add_trans fm Index.Left;
        let matches_ll = Index.find_neg s in
        let matches_rl = if Eqrel.sym s then matches_ll else [] in
        let critical = Index.find_trans_rightonly s "" in
        let pairs = List.flatten (List.map (preunify mm1) critical) in
        List.flatten [
          List.map (mknode_negtrans L L fm) matches_ll;
          List.map (mknode_negtrans R L fm) matches_rl;
          List.flatten (List.map (fun (m, e) -> make_inst m e) pairs);
          [Stop];
        ]
      end else begin
        Index.add_trans fm Index.Right;
        let matches_rr = Index.find_neg s in
        let matches_lr = if Eqrel.sym s then matches_rr else [] in
        let critical = Index.find_trans_leftonly s "" in
        let pairs = List.flatten (List.map (preunify mm2) critical) in
        List.flatten [
          List.map (mknode_negtrans R R fm) matches_rr;
          List.map (mknode_negtrans L R fm) matches_lr;
          List.flatten (List.map (fun (m, e) -> make_inst m e) pairs);
          [Stop];
        ]
      end

  | Eapp (s, [(Emeta _ as e1); e2], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Right;
      let h2 = Index.get_head e2 in
      let matches_rr = find_negtrans_right s h2 in
      let matches_lr = if Eqrel.sym s then find_negtrans_left s h2 else [] in
      let critical = Index.find_trans_leftonly s h2 in
      let pairs = List.flatten (List.map (preunify e1) critical) in
      List.flatten [
        List.map (mknode_negtrans R R fm) matches_rr;
        List.map (mknode_negtrans L R fm) matches_lr;
        List.flatten (List.map (fun (m, e) -> make_inst m e) pairs);
        [Stop];
      ]

  | Eapp (s, [e1; (Emeta _ as e2)], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Left;
      let h1 = Index.get_head e1 in
      let matches_ll = find_negtrans_left s h1 in
      let matches_rl = if Eqrel.sym s then find_negtrans_right s h1 else [] in
      let critical = Index.find_trans_rightonly s h1 in
      let pairs = List.flatten (List.map (preunify e1) critical) in
      List.flatten [
        List.map (mknode_negtrans L L fm) matches_ll;
        List.map (mknode_negtrans R L fm) matches_rl;
        List.flatten (List.map (fun (m, e) -> make_inst m e) pairs);
        [Stop];
      ]

  | Eapp (s, [e1; e2], _) when Eqrel.trans s ->
      Index.add_trans fm Index.Both;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = find_negtrans_left s h1 in
      let matches_rr = find_negtrans_right s h2 in
      let matches_lr = if Eqrel.sym s then find_negtrans_left s h2 else [] in
      let matches_rl = if Eqrel.sym s then find_negtrans_right s h1 else [] in
      List.flatten [
        List.map (mknode_negtrans L L fm) matches_ll;
        List.map (mknode_negtrans L R fm) matches_lr;
        List.map (mknode_negtrans R L fm) matches_rl;
        List.map (mknode_negtrans R R fm) matches_rr;
        [Stop];
      ]

  | Enot (Eapp ("=", [e1; e2], _), _) ->
      Index.add_negtrans fm;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = find_trans_left "=" h1 in
      let matches_lr = find_trans_right "=" h1 in
      let matches_rl = find_trans_left "=" h2 in
      let matches_rr = find_trans_right "=" h2 in
      List.flatten [
        List.map (mknode_trans L L fm) matches_ll;
        List.map (mknode_trans L R fm) matches_lr;
        List.map (mknode_trans R L fm) matches_rl;
        List.map (mknode_trans R R fm) matches_rr;
        [Stop];
      ]

  | Enot (Eapp (s, [e1; e2], _), _) when Eqrel.trans s ->
      Index.add_negtrans fm;
      let h1 = Index.get_head e1 in
      let h2 = Index.get_head e2 in
      let matches_ll = find_trans_left s h1 in
      let matches_rr = find_trans_right s h2 in
      let matches_lr = if Eqrel.sym s then find_trans_right s h1 else [] in
      let matches_rl = if Eqrel.sym s then find_trans_left s h2 else [] in
      List.flatten [
        List.map (mknode_trans L L fm) matches_ll;
        List.map (mknode_trans L R fm) matches_lr;
        List.map (mknode_trans R L fm) matches_rl;
        List.map (mknode_trans R R fm) matches_rr;
        [Stop];
      ]

  | _ -> []
;;

let newnodes_match_sym fm =
  match fm with
  | Enot (Eapp (s, [a1; a2], _), _) when Eqrel.sym s ->
      let do_match p = make_notequiv true p fm in
      List.flatten (List.map do_match (Index.find_pos s))
  | Eapp (s, [a1; a2], _) when Eqrel.sym s ->
      let do_match p = make_notequiv true fm p in
      List.flatten (List.map do_match (Index.find_neg s))
  | _ -> []
;;

let newnodes_match fm =
  match fm with
  | Enot (Eapp (s, _, _), _) ->
      let do_match p = make_notequiv false p fm in
      List.flatten (List.map do_match (Index.find_pos s)) @@ [Stop]
  | Eapp (s, _, _) ->
      let do_match p = make_notequiv false fm p in
      List.flatten (List.map do_match (Index.find_neg s)) @@ [Stop]
  | _ -> []
;;

let newnodes_useless fm =
  match fm with
  | Evar (v, _) -> [Stop]            (* propositional variable *)
  | Enot (Evar (v, _), _) -> [Stop]  (* propositional variable *)

  | Etrue -> [Stop]
  | Enot (Efalse, _) -> [Stop]

  | Emeta _ | Etau _
  | Enot ((Emeta _ | Etau _), _) ->
      if !Globals.warnings_flag then begin
        printf "add_nodes: unexpected formula meta/tau";
        Print.expr fm;
        printf "\n";
      end;
      [Stop]
  | _ -> []
;;

let add_nodes q noback fm =
  let newnodes1 =
    List.map (fun f -> lazy (f fm)) [
      newnodes_absurd;
      newnodes_closure;
    ] in
  let newnodes2 = Extension.newnodes !cur_depth fm in
  let newnodes3 =
    List.map (fun f -> lazy (f fm)) [
      newnodes_jtree;
      newnodes_alpha;
      newnodes_beta;
      newnodes_delta;
      newnodes_gamma;
      newnodes_unfold;
      newnodes_refl;
      newnodes_match_congruence;
      newnodes_match_trans;
      newnodes_match_sym;
      newnodes_match;
      newnodes_useless;
    ] in
  let goodnodes = Node.relevant (newnodes1 @ (newnodes2 @ newnodes3)) in
  let add_node q n =
    Index.add_branches n.nbranches;
    Heap.insert q (add_back noback n)
  in
  List.fold_left add_node q goodnodes
;;

(* goalness comme facteur multiplicatif ca ne marche pas car ca multiplie
   le facteur de type avec la taille.
*)
let order_nodes n1 n2 =
  let w1 = float n1.sprio (* *. (float n1.sgoalness /. 1e6 +. 0.5) *) in
  let w2 = float n2.sprio (* *. (float n2.sgoalness /. 1e6 +. 0.5) *) in
  if w1 < w2 then -1
  else if w1 > w2 then 1
  else 0
;;

let rec reduce_list accu l =
  match l with
  | [] -> accu
  | Enot (Efalse, _) :: t -> reduce_list accu t
  | Eapp ("=", [e1; e2], _) :: t when Expr.equal e1 e2 -> reduce_list accu t
  | Eapp ("=", [e1; e2], _) as f :: t ->
     let g = eapp ("=", [e2; e1]) in
     if Index.member f || Index.member g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | Enot (Eapp ("=", [e1; e2], _), _) as f :: t ->
     let g = enot (eapp ("=", [e2; e1])) in
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
  let reduced = Array.map (reduce_list []) n.sbranches in
  let rec array_exists f a i =
    if i >= Array.length a then false
    else if f a.(i) then true
    else array_exists f a (i+1)
  in
  if array_exists (function [] -> true | _ -> false) reduced 0
  then None
  else Some { n with sbranches = reduced }
;;

let rec count_metas accu ee =
  match ee with
  | Evar _ -> accu
  | Emeta _ -> accu + 1
  | Eapp (_, args, _) -> List.fold_left count_metas accu args
  | Enot (e, _) -> count_metas accu e
  | Eand (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eor (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eimply (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eequiv (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Etrue -> accu
  | Efalse -> accu
  | Eall (_, _, e, _) -> count_metas accu e
  | Eex (_, _, e, _) -> count_metas accu e
  | Etau (_, _, e, _) -> count_metas accu e
;;

let find_open_branch node state =
  let last = Array.length state - 1 in
  let rec loop accu i =
    if i < 0 then accu
    else if _equal state.(i) Open then loop (i::accu) (i-1)
    else loop accu (i-1)
  in
  let open_branches = loop [] last in
  match open_branches with
  | [] -> None
  | [i] -> Some (i, true)
  | l ->
(*
      let is_impl = match node.sconc with
                    | [Eimply _] -> true
                    | _ -> false
      in
*)
      let rec loop best best_score l =
        match l with
        | [] -> Some (best, false)
        | i::t ->
            let s1 = Index.get_branches node.sbranches.(i) in
(*
            let s5 = - List.fold_left count_metas 0 node.sbranches.(i) in
            let score = s1 + s5 in
*)
            let score = s1 in
            if score > best_score
            then loop i score t
            else loop best best_score t
      in
      (*if is_impl && state.(last) = Open then Some (last, false) else*)
      loop (-1) min_int l
;;

let rec open_one_back_branch node state i =
  assert (i < Array.length state);
  match state.(i) with
  | Back _ -> state.(i) <- Open
  | _ -> open_one_back_branch node state (i+1);
;;

let good_lemma rule =
  match rule with
  | Close _ | Close_refl _ | Close_sym _ | False | NotTrue -> false
  | _ -> true
;;

(* there is no [Open] in [branches];
   if there are [Back] values, merge them
   else make a proof node
*)
let make_result n nbranches =
  let backs = ref []
  and has_back = ref false;
  and concs = ref []
  and proofs = ref []
  in
  for i = 0 to Array.length nbranches - 1 do
    match nbranches.(i) with
    | Open -> assert false
    | Back (fms) ->
        has_back := true;
        backs := union (diff fms n.sbranches.(i)) !backs;
    | Closed p ->
        proofs := p :: !proofs;
        concs := union (diff p.mlconc n.sbranches.(i)) !concs;
  done;
  if not !has_back then begin
    assert (List.length !proofs == Array.length n.sbranches);
    let prf_node = {
      mlconc = union n.sconc !concs;
      mlrule = n.srule;
      mlhyps = Array.of_list (List.rev !proofs);
      mlrefc = 1;
    } in
    incr Globals.proof_nodes;
    if good_lemma n.srule then begin
      Index.add_proof prf_node;
    end;
    Closed prf_node
  end else begin
    Back (union n.sconc !backs)
  end
;;

let good_head q =
  match Heap.head q with
  | None -> true
  | Some node -> good_lemma node.srule
;;

let add_metas n =
  match n.srule with
  | All (p, Emeta (f, _)) | NotEx (p, Emeta (f, _)) when Expr.equal p f ->
      Index.add_meta f !cur_depth;
  | _ -> ()
;;

exception NoProof;;

let progress_counter = ref 10000;;

let rec refute_aux noback stk q forms =
  match forms with
  | [] ->
      if good_head q then begin
        match Index.search_proof () with
        | Some p -> p.mlrefc <- p.mlrefc + 1; unwind stk (Closed p)
        | None -> next_node stk q
      end else begin
        next_node stk q
      end
  | (Eapp (s, [e1; e2], _), _) :: fms when Eqrel.refl s && Expr.equal e1 e2 ->
       refute_aux noback stk q fms
  | (Eapp (s, args, _) as fm, _) :: fms when pure_meta args && not noback ->
      unwind stk (Back ([fm]))
  | (fm, g) :: fms ->
      Index.add fm g;
      Extension.add_formula fm;
      refute_aux noback stk (add_nodes q noback fm) fms

and refute noback stk q forms =
  Step.forms "refute" forms;
  decr progress_counter;
  if !progress_counter < 0 then begin
    progress_counter := 1000;
    Globals.do_progress (fun () -> ());
  end;
  refute_aux noback stk q forms

and next_node stk q =
  incr Globals.inferences;
  match Heap.remove q with
  | None -> raise NoProof
  | Some (n, q1) ->
      Index.remove_branches n.sbranches;
      let state = Array.make (Array.length n.sbranches) Open in
      match reduce_branches n with
      | Some n1 ->
          add_metas n1;
          next_branch stk n1 q1 state
      | None -> next_node stk q1    (* FIXME add_branches count becomes wrong *)

and next_branch stk n q state =
  Step.rule "next_branch" n.srule;
  match find_open_branch n state with
  | Some (i, is_last) ->
      let fr = {node = n; queue = q; state = state; cur = i} in
      incr cur_depth;
      if !cur_depth > !top_depth then top_depth := !cur_depth;
      let noback = is_last && n.snobacktrack in
      let branches = List.map (fun e -> (e, n.sgoalness)) n.sbranches.(i) in
      refute noback (fr :: stk) q branches
  | None ->
      let result = make_result n state in
      if n.snobacktrack && (match result with Back _ -> true | _ -> false)
      then begin
        open_one_back_branch n state 0;
        next_branch stk n q state
      end else begin
        unwind stk result
      end

and unwind stk res =
  match stk with
  | [] -> res
  | fr :: stk1 ->
      Step.rule "unwind" fr.node.srule;
      let f x =
        if Index.member x then begin (* we can unwind before adding all forms *)
          Extension.remove_formula x;
          Index.remove x;
        end;
      in
      List.iter f (List.rev fr.node.sbranches.(fr.cur));
      begin match fr.node.srule with
      | All (p, Emeta (f, _)) | NotEx (p, Emeta (f, _)) when Expr.equal p f ->
          Index.remove_meta f;
      | _ -> ()
      end;
      decr cur_depth;
      begin match res with
      | Closed p when disjoint fr.node.sbranches.(fr.cur) p.mlconc ->
          unwind stk1 res
      | Back (fms) when disjoint fr.node.sbranches.(fr.cur) fms ->
          unwind stk1 res
      | Closed _ ->
          fr.state.(fr.cur) <- res;
          next_branch stk1 fr.node fr.queue fr.state
      | Back _ ->
          fr.state.(fr.cur) <- res;
          next_branch stk1 fr.node fr.queue fr.state
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

let ticker () =
  let tm = Sys.time () in
  let heap_size = (Gc.stat ()).Gc.heap_words in  (* FIXME use Gc.quick_stat *)
  Globals.do_progress begin fun () ->
    eprintf "depth %5d/%d  search %d  proof %d  \
             lemma %d  size %dM  time %.0f\n"
            !cur_depth !top_depth !Globals.inferences !Globals.proof_nodes 
            !Globals.stored_lemmas (heap_size / 1_000_000) tm;
  end;
  if tm > !Globals.time_limit then begin
    eprintf " time limit exceeded\n";
    flush stderr;
    raise NoProof;
  end;
  if float heap_size > !Globals.size_limit then begin
    eprintf " size limit exceeded\n";
    flush stderr;
    raise NoProof;
  end;
;;

let make_goalness l =
  let check (_, g) =
    if g < 0 || g >= 1000
    then failwith (sprintf "goalness out of range %d" g)
  in
  List.iter check l;
  let mx = List.fold_left (fun m (_, g) -> max m g) 1 l in
  List.map (fun (e, g) -> (e, g * 1_000_000 / mx)) l
;;

let prove defs l =
  try
    List.iter Index.add_def defs;
    let al = Gc.create_alarm ticker in
    let rl = reduce_initial_list [] l in
    let wl = make_goalness rl in
    Globals.inferences := 0;
    Globals.proof_nodes := 0;
    cur_depth := 0;
    top_depth := 0;
    let result = refute false [] (Heap.empty order_nodes) wl in
    Gc.delete_alarm al;
    ticker ();
    Globals.end_progress "";
    match result with
    | Closed p -> p
    | Back _ -> assert false
    | Open -> assert false
  with NoProof ->
    Globals.end_progress " search failed";
    raise NoProof
;;
