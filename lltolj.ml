open Printf;;
open Expr;;
open Llproof;;
open Namespace;;

exception Found of expr;;

type sequent = expr list * expr list

type lkrule =
| SCAxiom of expr
| SCFalse
| SCTrue
| SCEqref of expr
| SCEqsym of expr * expr
| SCEqprop of expr * expr * lkrule list
| SCEqfunc of expr * expr * lkrule list
| SCCut of expr * lkrule * lkrule
| SCLand of expr * expr * lkrule
| SCLor of expr * expr * lkrule * lkrule
| SCLimply of expr * expr * lkrule * lkrule
| SCLnot of expr * lkrule
| SCLall of expr * expr * lkrule
| SCLex of expr * expr * lkrule
| SCLcongruence of expr * expr * expr * lkrule
| SCRand of expr * expr * lkrule * lkrule
| SCRorl of expr * expr * lkrule
| SCRorr of expr * expr * lkrule
| SCRimply of expr * expr * lkrule
| SCRnot of expr * lkrule
| SCRall of expr * expr * lkrule
| SCRex of expr * expr * lkrule
| SCRweak of expr * lkrule
| SCRcontr of expr * lkrule
;;

let lemma_env = 
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)
;;

let hypothesis_env = ref [];;

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)
;;

let applytohyps f lkrule =
  match lkrule with
  | SCAxiom (e) -> SCAxiom (e)
  | SCFalse -> SCFalse
  | SCTrue -> SCTrue
  | SCEqref (e) -> SCEqref (e)
  | SCEqsym (e1, e2) -> SCEqsym (e1, e2)
  | SCEqprop (e1, e2, lkrules) -> 
    SCEqprop (e1, e2, List.map f lkrules)
  | SCEqfunc (e1, e2, lkrules) -> 
    SCEqfunc (e1, e2, List.map f lkrules)
  | SCCut (e, rule1, rule2) -> 
    SCCut (e, f rule1, f rule2)
  | SCLand (e1, e2, rule) ->
    SCLand (e1, e2, f rule)
  | SCLor (e1, e2, rule1, rule2) ->
    SCLor (e1, e2, f rule1, f rule2)
  | SCLimply (e1, e2, rule1, rule2) ->
    SCLimply (e1, e2, f rule1, f rule2)
  | SCLnot (e, rule) -> SCLnot (e, f rule)
  | SCLall (e1, e2, rule) -> SCLall (e1, e2, f rule)
  | SCLex (e1, e2, rule) -> SCLex (e1, e2, f rule)
  | SCLcongruence (p, a, b, rule) -> SCLcongruence (p, a, b, f rule)
  | SCRand (e1, e2, rule1, rule2) ->
    SCRand (e1, e2, f rule1, f rule2)
  | SCRorl (e1, e2, rule) -> 
    SCRorl (e1, e2, f rule)
  | SCRorr (e1, e2, rule) ->
    SCRorr (e1, e2, f rule)
  | SCRimply (e1, e2, rule) ->
    SCRimply (e1, e2, f rule)
  | SCRnot (e, rule) -> SCRnot (e, f rule)
  | SCRall (e1, e2, rule) -> SCRall (e1, e2, f rule)
  | SCRex (e1, e2, rule) -> SCRex (e1, e2, f rule)
  | SCRweak (e, rule) -> SCRweak (e, f rule)
  | SCRcontr (e, rule) -> SCRcontr (e, f rule)
;;

let rec use_defs e = 
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v -> 
    let (params, body) = Hashtbl.find definition_env v in
    body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    substitute (List.combine params exprs) body
  | Evar (_, _) | Etrue | Efalse -> e
  | Eapp (s, args, _) ->
    eapp (s, List.map use_defs args)
  | Enot (e, _) ->
    enot (use_defs e)
  | Eand (e1, e2, _) ->
    eand (use_defs e1, use_defs e2)
  | Eor (e1, e2, _) ->
    eor (use_defs e1, use_defs e2)
  | Eimply (e1, e2, _) ->
    eimply (use_defs e1, use_defs e2)
  | Eequiv (e1, e2, _) ->
    let expr1 = use_defs e1 in
    let expr2 = use_defs e2 in
    eand (eimply (expr1, expr2), eimply (expr2, expr1))
  | Eall (x, s, e, _) ->
    eall (x, s, use_defs e)
  | Eex (x, s, e, _) ->
    eex (x, s, use_defs e)
  | Etau (x, s, e, _) ->
    etau (x, s, use_defs e)
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta _ -> 
    assert false

and use_defs_rule rule =
  match rule with
  | Rfalse | Rnottrue -> rule
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq _ | Reqsym _ -> rule
  | Rnotnot (p) -> Rnotnot (use_defs p)
  | Rconnect (b, p, q) -> Rconnect (b, use_defs p, use_defs q)
  | Rnotconnect (b, p, q) -> Rnotconnect (b, use_defs p, use_defs q)
  | Rex (ep, v) -> Rex (use_defs ep, use_defs v)
  | Rall (ap, t) -> Rall (use_defs ap, use_defs t)
  | Rnotex (ep, t) -> Rnotex (use_defs ep, use_defs t)
  | Rnotall (ap, v) -> Rnotall (use_defs ap, use_defs v)
  | Rpnotp (e1, e2) -> Rpnotp (use_defs e1, use_defs e2)
  | Rnotequal (e1, e2) -> Rnotequal (use_defs e1, use_defs e2)
  | RcongruenceLR (p, a, b) -> RcongruenceLR (use_defs p, a, b)
  | RcongruenceRL (p, a, b) -> RcongruenceRL (use_defs p, a, b)
  | Rdefinition _ -> rule
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map use_defs args, 
      List.map use_defs cons, List.map (List.map use_defs) hyps)
  | Rlemma (name, args) -> rule
;;

let rec lltolk proof =
  lltolkrule proof

and righttoleft e lkproof =
  SCLnot (e, lkproof)

and lefttoright expr lkrule =
  match lkrule with
  | SCLnot (e, rule) when equal (use_defs expr) (use_defs e) ->
    rule
  | SCAxiom (e) when equal (use_defs e) (enot (use_defs expr)) ->
    SCRnot (expr, SCAxiom (expr))
  | SCAxiom _ | SCFalse | SCTrue | SCEqref _ | SCEqsym _ -> 
    SCRweak (use_defs expr, lkrule)
  | _ -> applytohyps (lefttoright expr) lkrule

and lltolkrule proof =
  let hyps = List.map lltolkrule proof.hyps in
  match use_defs_rule proof.rule, hyps with
  | Rfalse, [] ->
    SCFalse
  | Rnottrue, [] -> 
    righttoleft etrue SCTrue
  | Raxiom (p), [] -> 
    righttoleft p (SCAxiom (p))
  | Rcut (p), [proof1; proof2] -> 
    SCCut (p, lefttoright p proof2, proof1)
  | Rnoteq (a), [] -> 
    righttoleft (eapp ("=", [a; a])) (SCEqref (a))
  | Reqsym (a, b), [] ->
    righttoleft (eapp ("=", [b; a]))
      (SCEqsym (a, b))
  | Rnotnot (p), [proof] ->
    righttoleft (enot (p))
      (SCRnot (p, proof))
  | Rconnect (And, p, q), [proof] ->
    SCLand (p, q, proof)
  | Rconnect (Or, p, q), [proof1; proof2] ->
    SCLor (p, q, proof1, proof2)
  | Rconnect (Imply, p, q), [proof1; proof2] ->
    SCLimply (p, q, lefttoright p proof1, proof2)
  | Rconnect (Equiv, p, q), [proof1; proof2] ->
    SCLand (
      eimply (p, q), eimply (q, p),
      SCLimply (
	p, q,
	SCLimply (
	  q, p, lefttoright p (lefttoright q proof1), SCAxiom (p)),
	SCLimply (q, p, SCAxiom (q), proof2)))
  | Rnotconnect (And, p, q), [proof1; proof2] ->
    righttoleft (eand (p, q))
      (SCRand (p, q, lefttoright p proof1, lefttoright q proof2))
  | Rnotconnect (Or, p, q), [proof] ->
    righttoleft (eor (p, q))
      (SCRcontr
	 (eor (p, q), SCRorl 
	   (p, q, SCRorr 
	     (p, q, lefttoright p (lefttoright q proof)))))
  | Rnotconnect (Imply, p, q), [proof] -> 
    righttoleft (eimply (p, q))
      (SCRimply (p, q, lefttoright q proof))
  | Rnotconnect (Equiv, p, q), [proof1; proof2] ->
    righttoleft (eequiv (p, q))
      (SCRand (eimply (p, q), eimply (q, p), 
	       SCRimply (p, q, lefttoright q proof2),
	       SCRimply (q, p, lefttoright p proof1)))
  | Rex (ep, v), [proof] ->
    SCLex (ep, v, proof)
  | Rall (ap, t), [proof] ->
    SCLall (ap, t, proof)
  | Rnotex (Eex(x, ty, p, _) as ep, t), [proof] ->
    righttoleft ep
      (SCRex (ep, t, lefttoright (substitute [(x, t)] p) proof))
  | Rnotall (Eall(x, ty, p, _) as ap, v), [proof] ->
    righttoleft ap
      (SCRall (ap, v, lefttoright (substitute [(x, v)] p) proof))
  | Rpnotp (Eapp (p, ts, _), Enot (Eapp (q, us, _), _)), proofs ->
    righttoleft (eapp (q, us))
      (SCEqprop (
	eapp (p, ts), eapp (q, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | Rnotequal (Eapp (f, ts, _), Eapp (g, us, _)), 
    proofs ->
    righttoleft (eapp ("=", [eapp (f, ts); eapp (g, us)]))
      (SCEqfunc (
	eapp (f, ts), eapp (g, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | RcongruenceLR (p, a, b), [proof] -> 
    SCLcongruence (p, a, b, proof)
  | RcongruenceRL (p, a, b), [proof] -> 
    SCCut (
      eapp ("=", [a; b]),
      SCEqsym (b, a),
      SCLcongruence (p, a, b, proof)) 
  | Rdefinition (name, sym, args, body, recarg, fld, unf), [proof] 
    -> proof
  | Rextension ("", "zenon_notallex", [Elam (v, t, p, _)], 
		[Enot (Eall (x, s, e, _) as ap, _)], [[ep]]), 
      [proof] ->
    let q = substitute [(v, etau (x, s, enot e))] p in
    righttoleft (ap)
      (SCRall (ap, etau (x, s, enot e), SCCut (
	ep,
	SCRex (
	  ep, etau (x, s, enot e), SCRnot (q, SCAxiom (q))),
	SCRweak (q, proof))))
  | Rextension (ext, name, args, cons, hyps), proofs -> 
    assert false
  | Rlemma (name, args), [] -> 
    let proof = Hashtbl.find lemma_env name in
    lltolkrule proof
  | _ -> assert false
;;

let rec ll e = match use_defs e with
  | Etrue -> enot (enot (etrue))
  | Efalse -> enot (enot (efalse))
  | Evar (s, _) -> evar (s);
  | Eapp ("=", args, _) -> enot (enot (eapp ("=", args)))
  | Eapp (s, args, _) -> eapp (s, args)
  | Eand (e1, e2, _) -> 
    enot (enot (eand (enot (enot (ll e1)),enot (enot (ll e2)))))
  | Eor (e1, e2, _) ->
    enot (enot (eor (enot (enot (ll e1)),enot (enot (ll e2)))))
  | Eimply (e1, e2, _) ->
    enot (enot (eimply (enot (enot (ll e1)),enot (enot (ll e2)))))
  | Eequiv (e1, e2, _) -> 
    ll (eand (eimply (e1, e2), eimply (e2, e1)))
  | Enot (e1, _) -> enot (enot (enot (enot (enot (ll e1)))))
  | Eall (Evar (v, _), s, e, _) ->
    enot (enot (eall (evar (v), s, enot (enot (ll e)))))
  | Eex (Evar (v, _), s, e, _) ->
    enot (enot (eex (evar (v), s, enot (enot (ll e)))))
  | Eex _ | Eall _ | Etau _ | Elam _ | Emeta _ -> 
    assert false

and l e = match use_defs e with
  | Etrue -> etrue
  | Efalse -> efalse
  | Evar (s, _) -> evar (s);
  | Eapp (s, args, _) -> eapp (s, args)
  | Eand (e1, e2, _) -> 
    eand (enot (enot (ll e1)),enot (enot (ll e2)))
  | Eor (e1, e2, _) -> 
    eor (enot (enot (ll e1)),enot (enot (ll e2)))
  | Eimply (e1, e2, _) -> 
    eimply (enot (enot (ll e1)),enot (enot (ll e2)))
  | Eequiv (e1, e2, _) -> 
    l (eand (eimply (e1, e2), eimply (e2, e1)))
  | Enot (e1, _) -> enot (enot (enot (ll e1)))
  | Eall (Evar (v, _), s, e, _) ->
    eall (evar (v), s, enot (enot (ll e)))
  | Eex (Evar (v, _), s, e, _) ->
    eex (evar (v), s, enot (enot (ll e)))
  | Eex _ | Eall _ | Etau _ | Elam _ | Emeta _ -> 
    assert false
;;

let lnotnot e rule =
  SCLnot (enot (e), SCRnot (e, rule))
;;

let lll e f rule=
  if equal (l e) (ll e)
  then rule 
  else f rule
;;

let rec lltolj proof goal =
  let conc, lkproof = List.fold_left 
    (fun (conc, rule) stmt -> 
      eimply (stmt, conc), SCRimply (stmt, conc, rule))
    (goal, lefttoright goal (lltolk proof)) !hypothesis_env in
  ll conc, SCRnot (
    enot (l conc),
    lltoljrule (lkproof))

and lltoljrule proof =
  match applytohyps lltoljrule proof with
  | SCAxiom (e) -> righttoleft (l e) (SCAxiom (l e))
  | SCFalse -> SCFalse
  | SCTrue -> 
    righttoleft (etrue) SCTrue
  | SCEqref (a) -> 
    righttoleft (eapp ("=", [a; a])) (SCEqref (a))
  | SCEqsym (a, b) ->
    righttoleft (eapp ("=", [b; a])) (SCEqsym (a, b))
  | SCCut (e, rule1, rule2) ->
    SCCut (enot (l e), SCRnot (l e, rule2), rule1)
  | SCLand (e1, e2, rule) ->
    SCLand 
      (enot (enot (ll e1)), enot (enot (ll e2)), 
       lnotnot (ll e1)
	 (lnotnot (ll e2)
	    (lll e1 (lnotnot (l e1))
	       (lll e2 (lnotnot (l e2)) rule))))
  | SCLor (e1, e2, rule1, rule2) ->
    SCLor (
      enot (enot (ll e1)), enot (enot (ll e2)),  
      lnotnot (ll e1)
        (lll e1 (lnotnot (l e1)) rule1),
      lnotnot (ll e2)
	(lll e2 (lnotnot (l e2)) rule2))
  | SCLimply (e1, e2, rule1, rule2) ->
    SCLimply (
      enot (enot (ll e1)), enot (enot (ll e2)),
      SCRnot (
	enot (ll e1),
	(lll e1 (lnotnot (enot (l e1))) rule1)),
      lnotnot (ll e2)
	(lll e2 (lnotnot (l e2)) rule2))
  | SCLnot (e, rule) ->
    lnotnot (enot (ll e))
      (lll e (lnotnot (enot (l e))) rule)
  | SCLall (Eall (x, ty, p, _) as ap, t, rule) ->
    let q = substitute [(x, t)] p in
    SCLall (
      l ap, t, 
      lnotnot (ll q)
	(lll q (lnotnot (l q)) rule))
  | SCLex (Eex (x, ty, p, _) as ep, v, rule) ->
    let q = substitute [(x, v)] p in
    SCLex (
      l ep, v,
      lnotnot (ll q)
	(lll q (lnotnot (l q)) rule))
  | SCLcongruence (Elam (x, t, e, _), a, b, rule) -> 
    SCLcongruence (elam (x, t, l e), a, b, rule)
  | SCRand (e1, e2, rule1, rule2) ->
    righttoleft (l (eand (e1, e2)))
      (SCRand (
	enot (enot (ll e1)), enot (enot (ll e2)), 
	SCRnot (
	  enot (ll e1), 
	  (lll e1 (lnotnot (enot (l e1))) rule1)),
	SCRnot (
	  enot (ll e2), 
	  (lll e2 (lnotnot (enot (l e2))) rule2))))
  | SCRorl (e1, e2, rule) ->
    righttoleft (l (eor (e1, e2)))
      (SCRorl (
	enot (enot (ll e1)), enot (enot (ll e2)),
	SCRnot (
          enot (ll e1),
          (lll e1 (lnotnot (enot (l e1))) rule))))
  | SCRorr (e1, e2, rule) ->
    righttoleft (l (eor (e1, e2)))
      (SCRorr (
	enot (enot (ll e1)), enot (enot (ll e2)),
	SCRnot (
          enot (ll e2),
          (lll e2 (lnotnot (enot (l e2))) rule))))
  | SCRimply (e1, e2, rule) ->
    righttoleft (l (eimply (e1, e2)))
      (SCRimply (
	enot (enot (ll e1)), enot (enot (ll e2)),
	SCRnot (
	  enot (ll e2),
	  lll e2 (lnotnot (enot (l e2)))
	    (lnotnot (ll e1)
	       (lll e1 (lnotnot (l e1)) rule)))))
  | SCRnot (e, rule) ->
    lnotnot (enot (enot (ll e)))
      (lnotnot (ll e)
	 (lll e (lnotnot (l e)) rule))
  | SCRall (Eall (x, ty, p, _) as ap, v, rule) ->
    let q = substitute [(x, v)] p in
    righttoleft (l ap)
      (SCRall (
	l ap, v,
	SCRnot (
	  enot (ll q), 
	  lll q (lnotnot (enot (l q))) rule)))
  | SCRex (Eex (x, ty, p, _) as ep, t, rule) ->
    let q = substitute [(x, t)] p in
    righttoleft (l ep)
      (SCRex (
	l ep, t,
	SCRnot (
	  enot (ll q), 
	  lll q (lnotnot (enot (l q))) rule)))
  | SCRweak (e, rule) -> rule
  | SCRcontr (e, rule) -> rule
  | _ -> assert false
;;
	
(*
let hypsofrule rule =
  match rule with
  | Rfalse -> []
  | Rnottrue -> []
  | Raxiom (p) -> []
  | Rcut (p) -> [[p]; [enot (p)]]
  | Rnoteq (a) -> []
  | Reqsym (a, b) -> []
  | Rnotnot (p) -> [[p]]
  | Rconnect (And, p, q) -> [[p; q]]
  | Rconnect (Or, p, q) -> [[p]; [q]]
  | Rconnect (Imply, p, q) -> [[enot (p)]; [q]]
  | Rconnect (Equiv, p, q) -> [[enot (p); enot(q)];[p; q]]
  | Rnotconnect (And, p, q) -> [[enot (p)]; [enot (q)]]
  | Rnotconnect (Or, p, q) -> [[enot (p); enot (q)]]
  | Rnotconnect (Imply, p, q) -> [[p; enot (q)]]
  | Rnotconnect (Equiv, p, q) -> [[enot (p); q]; [p; enot (q)]]
  | Rex (ep, v) -> []
  | Rall (ap, t) -> []
  | Rnotex (ep, t) -> []
  | Rnotall (ap, v) -> []
  | Rpnotp (p, q) -> []
  | Rnotequal (a, b) -> []
  | RcongruenceLR (p, a, b) -> []
  | RcongruenceRL (p, a, b) -> []
  | Rdefinition (name, sym, args, body, recarg, fld, unf) -> []
  | Rextension (ext, name, args, cons, hyps) -> []
  | Rlemma (name, args) -> []
;;
*)
