(*  Copyright 2004 INRIA  *)
Version.add "$Id: coqterm.ml,v 1.10 2004-06-29 09:50:34 prevosto Exp $";;

open Expr;;
open Llproof;;
open Printf;;

let prepend s1 s2 =
  if s1 = "" then s2
  else s1 ^ "_" ^ s2
;;

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

type coqproof = (string * coqterm) list * string * coqterm;;

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

let rec trtree prefix node =
  let {conc = conc; rule = rule; hyps = hyps} = node in
  match rule with
  | Rfalse -> getv (efalse)
  | Rnottrue -> Capp (Cvar "zenon_nottrue", [getv (enot (etrue))])
  | Raxiom (p) -> Capp (getv (enot p), [getv p])
  | Rnoteq (e) ->
      let e_neq_e = getv (enot (eapp ("=", [e; e]))) in
      Capp (Cvar "zenon_noteq", [Cwild; trexpr e; e_neq_e])
  | Rnotnot (p) ->
      let sub = mklam p (tr_subtree_1 prefix hyps) in
      Capp (getv (enot (enot p)), [sub])
  | Rconnect (And, p, q) ->
      let sub = mklam p (mklam q (tr_subtree_1 prefix hyps)) in
      Capp (Cvar "zenon_and", [tropt p; tropt q; sub; getv (eand (p, q))])
  | Rconnect (Or, p, q) ->
      let (subp, subq) = tr_subtree_2 prefix hyps in
      let lamp = mklam p subp in
      let lamq = mklam q subq in
      let concl = getv (eor (p, q)) in
      Capp (Cvar "zenon_or", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Imply, p , q) ->
      let (subp, subq) = tr_subtree_2 prefix hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam q subq in
      let concl = getv (eimply (p, q)) in
      Capp (Cvar "zenon_imply", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 prefix hyps in
      let lam1 = mklam (enot p) (mklam (enot q) sub1) in
      let lam2 = mklam p (mklam q sub2) in
      let concl = getv (eequiv (p, q)) in
      Capp (Cvar "zenon_equiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rnotconnect (And, p, q) ->
      let (subp, subq) = tr_subtree_2 prefix hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam (enot q) subq in
      let concl = getv (enot (eand (p, q))) in
      Capp (Cvar "zenon_notand", [tropt p; tropt q; lamp; lamq; concl])
  | Rnotconnect (Or, p, q) ->
      let sub = tr_subtree_1 prefix hyps in
      let lam = mklam (enot p) (mklam (enot q) sub) in
      let concl = getv (enot (eor (p, q))) in
      Capp (Cvar "zenon_notor", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Imply, p, q) ->
      let sub = tr_subtree_1 prefix hyps in
      let lam = mklam p (mklam (enot q) sub) in
      let concl = getv (enot (eimply (p, q))) in
      Capp (Cvar "zenon_notimply", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 prefix hyps in
      let lam1 = mklam (enot p) (mklam q sub1) in
      let lam2 = mklam p (mklam (enot q) sub2) in
      let concl = getv (enot (eequiv (p, q))) in
      Capp (Cvar "zenon_notequiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rex (Eex (x, ty, px, _) as exp, z) ->
      let sub = tr_subtree_1 prefix hyps in
      let pz = substitute [(x, evar z)] px in
      let lam = Clam (z, Cty ty, mklam pz sub) in
      Capp (Cvar "zenon_ex", [Cty ty; trpred x ty px; lam; getv exp])
  | Rex _ -> assert false
  | Rnotall (Eall (x, ty, px, _) as allp, z) ->
      let sub = tr_subtree_1 prefix hyps in
      let npz = enot (substitute [(x, evar z)] px) in
      let lam = Clam (z, Cty ty, mklam npz sub) in
      let concl = getv (enot allp) in
      Capp (Cvar "zenon_notall", [Cty ty; trpred x ty px; lam; concl])
  | Rnotall _ -> assert false
  | Rall (Eall (x, ty, px, _) as allp, t) ->
      let sub = tr_subtree_1 prefix hyps in
      let pt = substitute [(x, t)] px in
      let lam = mklam pt sub in
      let p = trpred x ty px in
      let concl = getv allp in
      Capp (Cvar "zenon_all", [Cty ty; p; trexpr t; lam; concl])
  | Rall _ -> assert false
  | Rnotex (Eex (x, ty, px, _) as exp, t) ->
      let sub = tr_subtree_1 prefix hyps in
      let npt = enot (substitute [(x, t)] px) in
      let lam = mklam npt sub in
      let p = trpred x ty px in
      let concl = getv (enot (exp)) in
      Capp (Cvar "zenon_notex", [Cty ty; p; trexpr t; lam; concl])
  | Rnotex _ -> assert false
  | Rpnotp ((Eapp (p, args1, _) as pp),
            (Enot (Eapp (q, args2, _) as qq, _) as nqq)) ->
      assert (p = q);      (*NdV: ajout Cwild *)
      let peq = Capp (Cvar "refl_equal", [Cwild; Cvar p]) in
      let ppeqq = make_equals prefix peq (Cvar p) args1 (Cvar p) args2 hyps in
      let vp = getv pp in
      let vnq = getv nqq in
      Capp (Cvar "zenon_pnotp", [tropt pp; tropt qq; ppeqq; vp; vnq])
  | Rpnotp _ -> assert false
  | Rnotequal ((Eapp (f, args1, _) as ff), (Eapp (g, args2, _) as gg)) ->
      assert (f = g);
      (*NdV: ajout Cwild *)
      let feg = Capp (Cvar "refl_equal", [Cwild; Cvar f]) in
      let ffegg = make_equals prefix feg (Cvar f) args1 (Cvar f) args2 hyps in
      let fdg = getv (enot (eapp ("=", [ff; gg]))) in
      let optf = tropt ff in
      let optg = tropt gg in
      Capp (Cvar "zenon_notequal", [Cwild; optf; optg; ffegg; fdg])
  | Rnotequal _ -> assert false
  | Requalnotequal (t, u, v, w) ->
      let (sub1, sub2) = tr_subtree_2 prefix hyps in
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
      let sub = tr_subtree_1 prefix hyps in
      Clet (getname unfolded, getv folded, sub)
  | Rextension (name, args, c, hs) ->
      let metargs = List.map trexpr args in
      let hypargs = List.map2 mklams hs (List.map (trtree prefix) hyps) in
      let conargs = List.map getv c in
      Capp (Cvar name, metargs @ hypargs @ conargs)
  | Rlemma (name, args) -> Hashtbl.find lemma_env (prepend prefix name)

and tr_subtree_1 prefix l =
  match l with
  | [t] -> trtree prefix t
  | _ -> assert false

and tr_subtree_2 prefix l =
  match l with
  | [t1; t2] -> (trtree prefix t1, trtree prefix t2)
  | _ -> assert false

and make_equals prefix peq p argsp q argsq hyps =
  match argsp, argsq, hyps with
  | [], [], [] -> peq
  | hp::tp, hq::tq, hh::th ->
      let thp = trexpr hp in
      let thq = trexpr hq in
      let lam = mklam (enot (eapp ("=", [hp; hq]))) (trtree prefix hh) in
      let neweq = Capp (Cvar "zenon_equal_step",
                        [Cwild; Cwild; p; q; thp; thq; peq; lam])
      in
      let newp = Capp (p, [thp]) in
      let newq = Capp (q, [thq]) in
      make_equals prefix neweq newp tp newq tq th
  | _, _, _ -> assert false
;;

let rec make_lambdas l term =
  match l with
  | [] -> term
  | (e, ty) :: t -> Clam (e, ty, make_lambdas t term)
;;

let compare_hyps (name1, _) (name2, _) = compare name1 name2;;

let make_lemma prefix { name = name; params = params; proof = proof } =
  let hyps = List.map (fun x -> (getname x, trexpr x)) proof.conc in
  let hyps1 = List.sort compare_hyps hyps in
  let pars = List.map (fun (x, y) -> (x, Cty y)) params in
  let formals = pars @ hyps1 in
  let actuals = List.map (fun (x, _) -> Cvar x) formals in
  (make_lambdas formals (trtree prefix proof), name, actuals)
;;

let rec trp prefix l =
  match l with
  | [th] ->
      let (thproof, thname, thargs) = make_lemma prefix th
      in ([], thproof, thname, thargs)
  | h::t ->
      let (lem, name, args) = make_lemma prefix h in
      let name1 = prepend prefix name in
      Hashtbl.add lemma_env name1 (Capp (Cvar name1, args));
      let (lemmas, thproof, thname, thargs) = trp prefix t in
      ((name1, lem) :: lemmas, thproof, thname, thargs)
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

let rec get_th_name = function
  | [] -> assert false
  | [h] -> h.name
  | _ :: t -> get_th_name t
;;

let trproof phrases l =
  Hashtbl.clear lemma_env;
  let prefix = get_th_name l in
  let (lemmas, raw, th_name, formals) = trp prefix l in
  let f = function
    | Cvar s -> find_name phrases s
    | _ -> assert false
  in
  let actuals = List.map f formals in
  let term = Capp (Cvar "NNPP", [Cwild;
                                 Clam ("_Zgoal", Cwild, Capp (raw, actuals))])
  in
  (lemmas, th_name, term)
;;

(* ******************************************* *)

let line_len = 72;;

let rem_len = ref line_len;;
let buf = Buffer.create 100;;
exception Cut_before of int;;
exception Cut_at of int;;

let test_cut j c =
  match c with
  | '('|')'|'~'|'>'|','|'['|']'|'?' -> raise (Cut_before (j+1))
  | ':'|'<' -> raise (Cut_before j)
  | ' ' -> raise (Cut_at j)
  | _ -> ()
;;
let init_buf () = rem_len := line_len;;
let flush_buf oc =
  let s = Buffer.contents buf in
  let len = String.length s in
  let i = ref 0 in
  while !i + !rem_len <= len do
    try
      for j = !rem_len - 1 downto 0 do
        test_cut j s.[!i + j];
      done;
      if !rem_len < line_len then raise (Cut_before 0);
      for j = !rem_len to len - !i - 1 do
        test_cut j s.[!i + j];
      done;
      raise (Cut_before (len - !i))
    with
    | Cut_before j ->
        output oc s !i j;
        i := !i + j;
        output_char oc '\n';
        rem_len := line_len;
    | Cut_at j ->
        output oc s !i j;
        i := !i + j + 1;
        output_char oc '\n';
        rem_len := line_len;
  done;
  output oc s !i (len - !i);
  rem_len := !rem_len - (len - !i);
  Buffer.clear buf;
;;

let rec get_lams accu t =
  match t with
  | Clam (s, ty, t1) -> get_lams ((s, ty) :: accu) t1
  | _ -> (List.rev accu, t)
;;

(* ******************************************* *)
    
module V8 = struct

  let pr_oc oc t =
    let rec pr b t =
      match t with
      | Cvar "" -> assert false
      | Cvar s -> bprintf b "%s" s; flush_buf oc;
      | Cty "" -> bprintf b "_U";
      | Cty s -> bprintf b "%s" s;
      | Clam (s, Cwild, t2) -> bprintf b "(fun %s=>%a)" s pr t2;
      | Clam (_, _, Clam _) ->
          let (lams, body) = get_lams [] t in
          bprintf b "(fun%a=>%a)" pr_lams lams pr body;
      | Clam (s, t1, t2) -> bprintf b "(fun %s:%a=>%a)" s pr t1 pr t2;
      | Capp (Cvar "=", [t1; t2]) -> bprintf b "(%a=%a)" pr t1 pr t2;
      | Capp (Cvar "not", [t1]) -> bprintf b "(~%a)" pr t1;
      | Capp (Cvar "and", [t1;t2]) -> bprintf b "(%a/\\%a)" pr t1 pr t2;
      | Capp (Cvar "or", [t1;t2]) -> bprintf b "(%a\\/%a)" pr t1 pr t2;
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
    init_buf ();
    pr buf t;
    flush_buf oc;
  ;;

  let print_one oc key (name, t) =
    fprintf oc "%s %s :=\n" key name;
    pr_oc oc t;
    fprintf oc ".\n";
  ;;

  let print outf (lemmas, thname, thproof) =
    let (oc, close_oc) = match outf with
      | None -> stdout, fun _ -> ()
      | Some f -> open_out f, close_out
    in
    if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
    List.iter (print_one oc "Let") lemmas;
    print_one oc "Definition" (thname, thproof);
    if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
    close_oc oc;
  ;;

end;;

(* ******************************************* *)

module V7 = struct

  let pr_oc oc t =
    let rec pr b t =
      match t with
      | Cvar "" -> assert false
      | Cvar s -> bprintf b "%s" s; flush_buf oc;
      | Cty "" -> bprintf b "_U";
      | Cty s -> bprintf b "%s" s;
      | Clam (s, Cwild, t2) -> bprintf b "([%s]%a)" s pr t2;
      | Clam (_, _, Clam _) ->
          let (lams, body) = get_lams [] t in
          bprintf b "(%a%a)" pr_lams lams pr body;
      | Clam (s, t1, t2) -> bprintf b "([%s:%a]%a)" s pr t1 pr t2;
      | Capp (Cvar "=", [t1; t2]) -> bprintf b "(%a=%a)" pr t1 pr t2;
      | Capp (Cvar "not", [t1]) -> bprintf b "(~%a)" pr t1;
      | Capp (Cvar "and", [t1;t2]) -> bprintf b "(%a/\\%a)" pr t1 pr t2;
      | Capp (Cvar "or", [t1;t2]) -> bprintf b "(%a\\/%a)" pr t1 pr t2;
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
    init_buf ();
    pr buf t;
    flush_buf oc;
  ;;

  let print_one oc key (name, t) =
    fprintf oc "%s %s :=\n" key name;
    pr_oc oc t;
    fprintf oc ".\n";
  ;;

  let print outf (lemmas, thname, thproof) =
    let (oc, close_oc) = match outf with
      | None -> stdout, fun _ -> ()
      | Some f -> open_out f, close_out
    in
    if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
    List.iter (print_one oc "Local") lemmas;
    print_one oc "Definition" (thname, thproof);
    if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
    close_oc oc;
  ;;

end;;
