(*  Copyright 2004 INRIA  *)
Version.add "$Id: coqterm.ml,v 1.4 2004-05-28 20:56:26 doligez Exp $";;

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

let getname e =
  let result = sprintf "_h%X" (Index.get_number e)
  in result;;
let getv e = Cvar (getname e);;

let is_meta s = String.length s >= 3 && String.sub s 0 3 = "_Z_";;

(* For now, [synthesize] is very simple-minded. *)
let synthesize s =
  let len = String.length s in
  assert (len > 3);
  let i = int_of_string (String.sub s 3 (len - 3)) in
  let ty = match Index.get_formula i with
           | Eall (_, ty, _, _) | Enot (Eex (_, ty, _, _), _) -> ty
           | _ -> assert false
  in
  match ty with
  | "" | "_U" -> Cvar "_any"
  | "nat" -> Cvar "(0)"
  | _ -> Cvar s
;;

let rec trexpr e =
  match e with
  | Evar (v, _) when is_meta v -> synthesize v
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

let tropt e = if !Globals.short_flag then Cwild else trexpr e;;
let trpred v ty p = Clam (v, Cty ty, trexpr p);;

let mklam v t = Clam (getname v, tropt v, t);;
let mklams args t = List.fold_right mklam args t;;

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
      Capp (Cvar "zenon_and", [tropt p; tropt q; sub; getv (eand (p, q))])
  | Rconnect (Or, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      let lamq = mklam q subq in
      let concl = getv (eor (p, q)) in
      Capp (Cvar "zenon_or", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Imply, p , q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam q subq in
      let concl = getv (eimply (p, q)) in
      Capp (Cvar "zenon_imply", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam (enot q) sub1) in
      let lam2 = mklam p (mklam q sub2) in
      let concl = getv (eequiv (p, q)) in
      Capp (Cvar "zenon_equiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rnotconnect (And, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam (enot q) subq in
      let concl = getv (enot (eand (p, q))) in
      Capp (Cvar "zenon_notand", [tropt p; tropt q; lamp; lamq; concl])
  | Rnotconnect (Or, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam (enot p) (mklam (enot q) sub) in
      let concl = getv (enot (eor (p, q))) in
      Capp (Cvar "zenon_notor", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Imply, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam p (mklam (enot q) sub) in
      let concl = getv (enot (eimply (p, q))) in
      Capp (Cvar "zenon_notimply", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam q sub1) in
      let lam2 = mklam p (mklam (enot q) sub2) in
      let concl = getv (enot (eequiv (p, q))) in
      Capp (Cvar "zenon_notequiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rex (Eex (x, ty, px, _) as exp, z) ->
      let sub = tr_subtree_1 hyps in
      let pz = substitute [(x, evar z)] px in
      let lam = Clam (z, Cty ty, mklam pz sub) in
      Capp (Cvar "zenon_ex", [Cty ty; trpred x ty px; lam; getv exp])
  | Rex _ -> assert false
  | Rnotall (Eall (x, ty, px, _) as allp, z) ->
      let sub = tr_subtree_1 hyps in
      let npz = enot (substitute [(x, evar z)] px) in
      let lam = Clam (z, Cty ty, mklam npz sub) in
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
      Capp (Cvar "zenon_pnotp", [tropt pp; tropt qq; ppeqq; vp; vnq])
  | Rpnotp _ -> assert false
  | Rnotequal ((Eapp (f, args1, _) as ff), (Eapp (g, args2, _) as gg)) ->
      assert (f = g);
      let feg = Capp (Cvar "refl_equal", [Cvar f]) in
      let ffegg = make_equals feg (Cvar f) args1 (Cvar f) args2 hyps in
      let fdg = getv (enot (eapp ("=", [ff; gg]))) in
      let optf = tropt ff in
      let optg = tropt gg in
      Capp (Cvar "zenon_notequal", [Cwild; optf; optg; ffegg; fdg])
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
            [Cwild; tropt t; tropt u; tropt v; tropt w; lam1; lam2; teu; vdw])
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
  (make_lambdas formals (trtree proof), name, actuals)
;;

let rec trp = function
  | [th] -> make_lemma th
  | h::t ->
      let (lem, name, args) = make_lemma h in
      Hashtbl.add lemma_env h.name (Capp (Cvar name, args));
      let (thproof, thname, thargs) = trp t in
      (Clet (h.name, lem, thproof), thname, thargs)
  | [] -> assert false
;;

let rec find_name phrases s =
  match phrases with
  | [] -> assert false
  | Phrase.Hyp (n, e, _) :: t ->
      let name = getname e in
      if name = s then Cvar n else find_name t s
  | _ :: t -> find_name t s
;;

let trproof phrases l =
  Hashtbl.clear lemma_env;
  let (raw, _, formals) = trp l in
  let f = function
    | Cvar s -> find_name phrases s
    | _ -> assert false
  in
  let actuals = List.map f formals in
  Capp (Cvar "NNPP", [Cwild; Clam ("_Zgoal", Cwild, Capp (raw, actuals))])
;;

(* ******************************************* *)

let rec get_lams accu t =
  match t with
  | Clam (s, ty, t1) -> get_lams ((s, ty) :: accu) t1
  | _ -> (List.rev accu, t)
;;

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

let buf = Buffer.create 100;;
let cur_col = ref 0;;
let rec cut_buf oc =
  let len = Buffer.length buf in
  let i = ref 0 in
  while !i < len do
    if !cur_col < 64 then begin
      let l = 64 - !cur_col in
      let l = if !i + l > len then len - !i else l in
      output_string oc (Buffer.sub buf !i l);
      i := !i + l;
      cur_col := !cur_col + l;
    end;
    if !i < len then begin
      match Buffer.nth buf !i with
      | ( '(' | ')' | '<' | ':' | '~' | '[' | ']' | '?') as c ->
          output_char oc '\n';
          cur_col := 0;
      | ' ' -> output_char oc '\n';
               cur_col := 0;
               incr i;
      | c -> output_char oc c;
             incr cur_col;
             incr i;
    end;
  done;
  Buffer.clear buf;
;;

module V8 = struct

  let pr_oc oc t =
    let rec pr b t =
      match t with
      | Cvar "" -> assert false
      | Cvar s -> bprintf b "%s" s; cut_buf oc;
      | Cty "" -> bprintf b "_U";
      | Cty s -> bprintf b "%s" s;
      | Clam (s, Cwild, t2) -> bprintf b "(fun %s=>%a)" s pr t2;
      | Clam (_, _, Clam _) ->
          let (lams, body) = get_lams [] t in
          bprintf b "(fun%a=>%a)" pr_lams lams pr body;
      | Clam (s, t1, t2) -> bprintf b "(fun %s:%a=>%a)" s pr t1 pr t2;
      | Capp (Cvar "=", [t1; t2]) -> bprintf b "(%a=%a)" pr t1 pr t2;
      | Capp (Cvar "not", [t1]) -> bprintf b "(~%a)" pr t1;
      | Capp (t1, []) -> pr b t1;
      | Capp (Capp (t1, args1), args2) -> pr b (Capp (t1, args1 @ args2));
      | Capp (t1, args) -> bprintf b "(%a%a)" pr t1 pr_list args;
      | Cimply (t1, t2) -> bprintf b "(%a->%a)" pr t1 pr t2;
      | Cequiv (t1, t2) -> bprintf b "(%a<->%a)" pr t1 pr t2;
      | Call (v, "", t1) -> bprintf b "(forall %s:_U,%a)" v pr t1;
      | Call (v, ty, t1) -> bprintf b "(forall %s:%s,%a)" v ty pr t1;
      | Cex (v, "", t1) -> bprintf b "(exists %s:_U,%a)" v pr t1;
      | Cex (v, ty, t1) -> bprintf b "(exists %s:%s,%a)" v ty pr t1;
      | Clet (v, t1, t2) -> bprintf b "(let %s:=%a in %a)" v pr t1 pr t2;
      | Cwild -> bprintf b "_";
    and pr_list b l =
      let f t = bprintf b " %a" pr t; in
      List.iter f l;
    and pr_lams b l =
      let f (v, ty) =
        match ty with
        | Cwild -> bprintf b " %s" v;
        | _ -> bprintf b "(%s:%a)" v pr ty;
      in
      List.iter f l;
    in
    pr buf t;
    cut_buf oc;
  ;;

  let print outf t = print_gen pr_oc outf t;;

end;;

(* ******************************************* *)

module V7 = struct

  let pr_oc oc t =
    let rec pr b t =
      match t with
      | Cvar "" -> assert false
      | Cvar s -> bprintf b "%s" s; cut_buf oc;
      | Cty "" -> bprintf b "_U";
      | Cty s -> bprintf b "%s" s;
      | Clam (s, Cwild, t2) -> bprintf b "([%s]%a)" s pr t2;
      | Clam (_, _, Clam _) ->
          let (lams, body) = get_lams [] t in
          bprintf b "(%a%a)" pr_lams lams pr body;
      | Clam (s, t1, t2) -> bprintf b "([%s:%a]%a)" s pr t1 pr t2;
      | Capp (Cvar "=", [t1; t2]) -> bprintf b "(%a=%a)" pr t1 pr t2;
      | Capp (Cvar "not", [t1]) -> bprintf b "(~%a)" pr t1;
      | Capp (t1, []) -> pr b t1;
      | Capp (Capp (t1, args1), args2) -> pr b (Capp (t1, args1 @ args2));
      | Capp (t1, args) -> bprintf b "(%a%a)" pr t1 pr_list args;
      | Cimply (t1, t2) -> bprintf b "(%a->%a)" pr t1 pr t2;
      | Cequiv (t1, t2) -> bprintf b "(%a<->%a)" pr t1 pr t2;
      | Call (v, "", t1) -> bprintf b "((%s:_U)%a)" v pr t1;
      | Call (v, ty, t1) -> bprintf b "((%s:%s)%a)" v ty pr t1;
      | Cex (v, "", t1) -> bprintf b "(Ex[%s:_U]%a)" v pr t1;
      | Cex (v, ty, t1) -> bprintf b "(Ex[%s:%s]%a)" v ty pr t1;
      | Clet (v, t1, t2) -> bprintf b "([%s:=%a]%a)" v pr t1 pr t2;
      | Cwild -> bprintf b "?";

    and pr_list b l =
      let f t = bprintf b " %a" pr t; in
      List.iter f l;

    and pr_lams b l =
       let f (v, ty) =
        match ty with
        | Cwild -> bprintf b "[%s]" v;
        | _ -> bprintf b "[%s:%a]" v pr ty;
      in
      List.iter f l;
    in
    pr buf t;
    cut_buf oc;
  ;;

  let print outf t = print_gen pr_oc outf t;;

end;;
