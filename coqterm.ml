(*  Copyright 2004 INRIA  *)
Version.add "$Id: coqterm.ml,v 1.2 2004-05-27 17:21:24 doligez Exp $";;

open Expr;;
open Llproof;;
open Printf;;

type coqterm =
  | Cvar of string
  | Cty of string
  | Clam of string * coqterm * coqterm
  | Capp of coqterm * coqterm list
  | Cimply of coqterm * coqterm
  | Cequiv of coqterm * coqterm
  | Call of string * string * coqterm
  | Cex of string * string * coqterm
  | Clet of string * coqterm * coqterm
  | Cwild
;;

let lemma_env = (Hashtbl.create 97 : (string, coqterm) Hashtbl.t);;

let getname e = Printf.sprintf "_h%X" (Index.get_number e);;
let getv e = Cvar (getname e);;

let rec trexpr e =
  match e with
  | Evar (v, _) -> Cvar v
  | Emeta (e1, _) -> assert false
  | Eapp (f, args, _) -> Capp (Cvar f, List.map trexpr args)
  | Enot (e1, _) -> Capp (Cvar "not", [trexpr e1])
  | Eand (e1, e2, _) -> Capp (Cvar "and", [trexpr e1; trexpr e2])
  | Eor (e1, e2, _) -> Capp (Cvar "or", [trexpr e1; trexpr e2])
  | Eimply (e1, e2, _) -> Cimply (trexpr e1, trexpr e2)
  | Eequiv (e1, e2, _) -> Cequiv (trexpr e1, trexpr e2)
  | Etrue -> Cvar "True"
  | Efalse -> Cvar "False"
  | Eall (v, t, e1, _) -> Call (v, t, trexpr e1)
  | Eex (v, t, e1, _) -> Cex (v, t, trexpr e1)
  | Etau (v, t, e1, _) -> assert false
;;

let mklam v t = Clam (getname v, trexpr v, t);;
let mklams args t = List.fold_right mklam args t;;

let trwild = trexpr;;
let trpred v ty p = Clam (v, Cvar ty, trexpr p);;

let rec trtree node =
  let {conc = conc; rule = rule; hyps = hyps} = node in
  match rule with
  | Rfalse -> getv (efalse)
  | Rnottrue -> Capp (Cvar "zenon_nottrue", [getv (enot (etrue))])
  | Raxiom (p) -> Capp (getv (enot p), [getv p])
  | Rnoteq (e) ->
      let e_neq_e = getv (enot (eapp ("=", [e; e]))) in
      Capp (Cvar "zenon_noteq", [Cwild; trexpr e; e_neq_e])
  | Rnotnot (p) ->
      let sub = mklam p (tr_subtree_1 hyps) in
      Capp (getv (enot (enot p)), [sub])
  | Rconnect (And, p, q) ->
      let sub = mklam p (mklam q (tr_subtree_1 hyps)) in
      Capp (Cvar "zenon_and", [trwild p; trwild q; sub; getv (eand (p, q))])
  | Rconnect (Or, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      let lamq = mklam q subq in
      let concl = getv (eor (p, q)) in
      Capp (Cvar "zenon_or", [trwild p; trwild q; lamp; lamq; concl])
  | Rconnect (Imply, p , q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam q subq in
      let concl = getv (eimply (p, q)) in
      Capp (Cvar "zenon_imply", [trwild p; trwild q; lamp; lamq; concl])
  | Rconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam (enot q) sub1) in
      let lam2 = mklam p (mklam q sub2) in
      let concl = getv (eequiv (p, q)) in
      Capp (Cvar "zenon_equiv", [trwild p; trwild q; lam1; lam2; concl])
  | Rnotconnect (And, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam (enot q) subq in
      let concl = getv (enot (eand (p, q))) in
      Capp (Cvar "zenon_notand", [trwild p; trwild q; lamp; lamq; concl])
  | Rnotconnect (Or, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam (enot p) (mklam (enot q) sub) in
      let concl = getv (enot (eor (p, q))) in
      Capp (Cvar "zenon_notor", [trwild p; trwild q; lam; concl])
  | Rnotconnect (Imply, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam p (mklam (enot q) sub) in
      let concl = getv (enot (eimply (p, q))) in
      Capp (Cvar "zenon_notimply", [trwild p; trwild q; lam; concl])
  | Rnotconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam q sub1) in
      let lam2 = mklam p (mklam (enot q) sub2) in
      let concl = getv (enot (eequiv (p, q))) in
      Capp (Cvar "zenon_notequiv", [trwild p; trwild q; lam1; lam2; concl])
  | Rex (Eex (x, ty, px, _) as exp, z) ->
      let sub = tr_subtree_1 hyps in
      let pz = substitute [(x, evar z)] px in
      let lam = Clam (z, Cvar ty, mklam pz sub) in
      Capp (Cvar "zenon_ex", [Cty ty; trpred x ty px; lam; getv exp])
  | Rex _ -> assert false
  | Rnotall (Eall (x, ty, px, _) as allp, z) ->
      let sub = tr_subtree_1 hyps in
      let npz = enot (substitute [(x, evar z)] px) in
      let lam = Clam (z, Cvar ty, mklam npz sub) in
      let concl = getv (enot allp) in
      Capp (Cvar "zenon_notall", [Cty ty; trpred x ty px; lam; concl])
  | Rnotall _ -> assert false
  | Rall (Eall (x, ty, px, _) as allp, t) ->
      let sub = tr_subtree_1 hyps in
      let pt = substitute [(x, t)] px in
      let lam = mklam pt sub in
      let p = trpred x ty px in
      let concl = getv allp in
      Capp (Cvar "zenon_all", [Cty ty; p; trexpr t; lam; concl])
  | Rall _ -> assert false
  | Rnotex (Eex (x, ty, px, _) as exp, t) ->
      let sub = tr_subtree_1 hyps in
      let npt = enot (substitute [(x, t)] px) in
      let lam = mklam npt sub in
      let p = trpred x ty px in
      let concl = getv (enot (exp)) in
      Capp (Cvar "zenon_notex", [Cty ty; p; trexpr t; lam; concl])
  | Rnotex _ -> assert false
  | Rpnotp ((Eapp (p, args1, _) as pp),
            (Enot (Eapp (q, args2, _) as qq, _) as nqq)) ->
      assert (p = q);
      let peq = Capp (Cvar "refl_equal", [Cvar p]) in
      let ppeqq = make_equals peq (Cvar p) args1 (Cvar p) args2 hyps in
      let vp = getv pp in
      let vnq = getv nqq in
      Capp (Cvar "zenon_pnotp", [trwild pp; trwild qq; ppeqq; vp; vnq])
  | Rpnotp _ -> assert false
  | Rnotequal ((Eapp (f, args1, _) as ff), (Eapp (g, args2, _) as gg)) ->
      assert (f = g);
      let feg = Capp (Cvar "refl_equal", [Cvar f]) in
      let ffegg = make_equals feg (Cvar f) args1 (Cvar f) args2 hyps in
      let fdg = getv (enot (eapp ("=", [ff; gg]))) in
      let wf = trwild ff in
      let wg = trwild gg in
      Capp (Cvar "zenon_notequal", [Cwild; wf; wg; ffegg; fdg])
  | Rnotequal _ -> assert false
  | Requalnotequal (t, u, v, w) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let tdv = enot (eapp ("=", [t; v])) in
      let udv = enot (eapp ("=", [u; v])) in
      let udw = enot (eapp ("=", [u; w])) in
      let tdw = enot (eapp ("=", [t; w])) in
      let lam1 = mklam tdv (mklam udv sub1) in
      let lam2 = mklam udw (mklam tdw sub2) in
      let teu = getv (eapp ("=", [t; u])) in
      let vdw = getv (enot (eapp ("=", [v; w]))) in
      Capp (Cvar "zenon_equalnotequal",
            [Cwild; trwild t; trwild u; trwild v; trwild w;
             lam1; lam2; teu; vdw])
  | Rdefinition (folded, unfolded) ->
      let sub = tr_subtree_1 hyps in
      Clet (getname unfolded, getv folded, sub)
  | Rextension (name, args, c, hs) ->
      let metargs = List.map trexpr args in
      let hypargs = List.map2 mklams hs (List.map trtree hyps) in
      let conargs = List.map getv c in
      Capp (Cvar name, metargs @ hypargs @ conargs)
  | Rlemma (name, args) -> Hashtbl.find lemma_env name

and tr_subtree_1 = function
  | [t] -> trtree t
  | _ -> assert false

and tr_subtree_2 = function
  | [t1; t2] -> (trtree t1, trtree t2)
  | _ -> assert false

and make_equals peq p argsp q argsq hyps =
  match argsp, argsq, hyps with
  | [], [], [] -> peq
  | hp::tp, hq::tq, hh::th ->
      let thp = trexpr hp in
      let thq = trexpr hq in
      let lam = mklam (enot (eapp ("=", [hp; hq]))) (trtree hh) in
      let neweq = Capp (Cvar "zenon_equal_step",
                        [Cwild; Cwild; p; q; thp; thq; peq; lam])
      in
      let newp = Capp (p, [thp]) in
      let newq = Capp (q, [thq]) in
      make_equals neweq newp tp newq tq th
  | _, _, _ -> assert false
;;

let rec make_lambdas l term =
  match l with
  | [] -> term
  | (e, ty) :: t -> Clam (e, ty, make_lambdas t term)
;;

let compare_hyps (name1, _) (name2, _) = compare name1 name2;;

let make_lemma { name = name; params = params; proof = proof } =
  let hyps = List.map (fun x -> (getname x, trexpr x)) proof.conc in
  let hyps1 = List.sort compare_hyps hyps in
  let pars = List.map (fun (x, y) -> (x, Cty y)) params in
  let formals = pars @ hyps1 in
  let actuals = List.map (fun (x, _) -> Cvar x) formals in
  (make_lambdas formals (trtree proof), Capp (Cvar name, actuals))
;;

let rec trp = function
  | [th] -> fst (make_lemma th)
  | h::t ->
      let (lem, use) = make_lemma h in
      Hashtbl.add lemma_env h.name use;
      Clet (h.name, lem, trp t)
  | [] -> assert false
;;

let rec find_name phrases s =
  match phrases with
  | [] -> assert false
  | Phrase.Hyp (n, e, _) :: t when getname e = s -> Cvar n
  | _ :: t -> find_name t s
;;

let rec get_lams accu t =
  match t with
  | Clam (s, ty, t1) -> get_lams ((s, ty) :: accu) t1
  | _ -> (List.rev accu, t)
;;

let trproof phrases l =
  Hashtbl.clear lemma_env;
  let raw = trp l in
  let (formals, _) = get_lams [] raw in
  let actuals = List.map (fun (s, ty) -> find_name phrases s) formals in
  Capp (Cvar "NNPP", [Cwild; Clam ("_Zgoal", Cwild, Capp (raw, actuals))])
;;

(* ******************************************* *)

let print_gen pr outf t =
  let (oc, close_oc) = match outf with
    | None -> stdout, fun _ -> ()
    | Some f -> open_out f, close_out
  in
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  pr oc t;
  if not !Globals.quiet_flag then fprintf oc "\n(* END-PROOF *)\n";
  close_oc oc;
;;

module V8 = struct
  let rec pr oc t =
    match t with
    | Cvar "" -> assert false
    | Cvar s -> fprintf oc "%s" s;
    | Cty "" -> fprintf oc "_U";
    | Cty s -> fprintf oc "%s" s;
    | Clam (s, Cwild, t2) -> fprintf oc "(fun %s =>\n%a)" s pr t2;
    | Clam (_, _, Clam _) ->
        let (lams, body) = get_lams [] t in
        fprintf oc "(fun%a =>\n%a)" pr_lams lams pr body;
    | Clam (s, t1, t2) -> fprintf oc "(fun %s : %a =>\n%a)" s pr t1 pr t2;
    | Capp (Cvar "=", [t1; t2]) -> fprintf oc "(%a = %a)" pr t1 pr t2;
    | Capp (Cvar "not", [t1]) -> fprintf oc "(~%a)" pr t1;
    | Capp (t1, []) -> pr oc t1
    | Capp (Capp (t1, args1), args2) -> pr oc (Capp (t1, args1 @ args2))
    | Capp (t1, args) -> fprintf oc "(%a%a)" pr t1 pr_list args;
    | Cimply (t1, t2) -> fprintf oc "(%a -> %a)" pr t1 pr t2;
    | Cequiv (t1, t2) -> fprintf oc "(%a <-> %a)" pr t1 pr t2;
    | Call (v, "", t1) -> fprintf oc "(forall %s : _U, %a)" v pr t1;
    | Call (v, ty, t1) -> fprintf oc "(forall %s : %s, %a)" v ty pr t1;
    | Cex (v, "", t1) -> fprintf oc "(exists %s : _U, %a)" v pr t1;
    | Cex (v, ty, t1) -> fprintf oc "(exists %s : %s, %a)" v ty pr t1;
    | Clet (v, t1, t2) -> fprintf oc "(let %s := %a\nin %a)" v pr t1 pr t2;
    | Cwild -> fprintf oc "_";

  and pr_list oc l =
    let f t = fprintf oc " %a" pr t; in
    List.iter f l;

  and pr_lams oc l =
    let f (v, ty) = fprintf oc " (%s : %a)" v pr ty; in
    List.iter f l;
  ;;

  let print outf t = print_gen pr outf t;;

end;;

(* ******************************************* *)

module V7 = struct
  let rec pr oc t =
    match t with
    | Cvar "" -> assert false
    | Cvar s -> fprintf oc "%s" s;
    | Cty "" -> fprintf oc "_U";
    | Cty s -> fprintf oc "%s" s;
    | Clam (s, Cwild, t2) -> fprintf oc "([%s]\n%a)" s pr t2;
    | Clam (_, _, Clam _) ->
        let (lams, body) = get_lams [] t in
        fprintf oc "(%a%a)" pr_lams lams pr body;
    | Clam (s, t1, t2) -> fprintf oc "([%s : %a]\n%a)" s pr t1 pr t2;
    | Capp (Cvar "=", [t1; t2]) -> fprintf oc "(%a = %a)" pr t1 pr t2;
    | Capp (Cvar "not", [t1]) -> fprintf oc "(~%a)" pr t1;
    | Capp (t1, []) -> pr oc t1
    | Capp (Capp (t1, args1), args2) -> pr oc (Capp (t1, args1 @ args2))
    | Capp (t1, args) -> fprintf oc "(%a%a)" pr t1 pr_list args;
    | Cimply (t1, t2) -> fprintf oc "(%a -> %a)" pr t1 pr t2;
    | Cequiv (t1, t2) -> fprintf oc "(%a <-> %a)" pr t1 pr t2;
    | Call (v, "", t1) -> fprintf oc "((%s : _U) %a)" v pr t1;
    | Call (v, ty, t1) -> fprintf oc "((%s : %s) %a)" v ty pr t1;
    | Cex (v, "", t1) -> fprintf oc "(exists [%s : _U] %a)" v pr t1;
    | Cex (v, ty, t1) -> fprintf oc "(exists [%s : %s] %a)" v ty pr t1;
    | Clet (v, t1, t2) -> fprintf oc "([%s := %a]\n%a)" v pr t1 pr t2;
    | Cwild -> fprintf oc "?";

  and pr_list oc l =
    let f t = fprintf oc " %a" pr t; in
    List.iter f l;

  and pr_lams oc l =
    let f (v, ty) = fprintf oc " [%s : %a]" v pr ty; in
    List.iter f l;
  ;;

  let print outf t = print_gen pr outf t;;

end;;
