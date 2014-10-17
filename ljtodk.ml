open Printf
open Expr

module Dk = Dkterm

let rec trexpr e =
  match e with
  | Eand (Eimply (e1, e2, _), Eimply (e3, e4, _), _)
    when (equal e3 e2 && equal e4 e1) -> Dk.dkequiv (trexpr e1) (trexpr e2)
  | Enot (Enot (Enot (Enot (Enot (e, _), _), _), _), _) ->
    Dk.dknotc (trexpr e)
  | Enot (Enot ( Eand (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkandc (trexpr e1) (trexpr e2)
  | Enot (Enot ( Eor (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkorc (trexpr e1) (trexpr e2)
  | Enot (Enot ( Eimply (
    Enot (Enot (e1, _), _), Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkimplyc (trexpr e1) (trexpr e2)
  | Enot (Enot (Etrue, _), _) -> Dk.dktruec
  | Enot (Enot (Efalse, _), _) -> Dk.dkfalsec
  | Enot (Enot (
    Eall (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkforallc (trexpr e1) (trexpr e2)
  | Enot (Enot (
    Eex (e1, s, Enot (Enot (e2, _), _), _), _), _) ->
    Dk.dkexistsc (trexpr e1) (trexpr e2)
  | Enot (Enot (Eapp ("=", [e1;e2], _), _), _) ->
    Dk.dkeqc (trexpr e1) (trexpr e2)
  | Evar (v, _) when Mltoll.is_meta v ->
    Dk.dkanyterm
  | Evar (v, _) ->
    Dk.dkvar v
  | Eapp ("$string", [Evar (v, _)], _) ->
    Dk.dkvar ("S"^v)
  | Eapp ("$string", _, _) -> assert false
  | Eapp ("=", [e1;e2], _) ->
    Dk.dkeq (trexpr e1) (trexpr e2)
  | Eapp (s, args, _) ->
    Dk.dkapp (Dk.dkvar s) (List.map trexpr args)
  | Enot (e, _) ->
    Dk.dknot (trexpr e)
  | Eand (e1, e2, _) ->
    Dk.dkand (trexpr e1) (trexpr e2)
  | Eor (e1, e2, _) ->
    Dk.dkor (trexpr e1) (trexpr e2)
  | Eimply (e1, e2, _) ->
    Dk.dkimply (trexpr e1) (trexpr e2)
  | Etrue -> Dk.dktrue
  | Efalse -> Dk.dkfalse
  | Eall (e1, s, e2, _) ->
    Dk.dkforall (trexpr e1) (trexpr e2)
  | Eex (e1, s, e2, _) ->
    Dk.dkexists (trexpr e1) (trexpr e2)
  | Elam _ | Eequiv _ | Emeta _ | Etau _ -> assert false

let new_name =
  let r = ref 0 in
  fun () ->
    let n = !r in
    incr r; n

let new_hypo () = sprintf "H%d" (new_name ())
let new_prop () = sprintf "P%d" (new_name ())
let new_term () = sprintf "X%d" (new_name ())

(* the left part of sequents can only grow: the left part of the conclusion is always contained in the left part of the hypothesis
weakening is implicit*)

let rec trproof (lkproof, goal, gamma) =
  let g, d, lkrule = lkproof in
  let trhyp e =
    try (List.assoc e gamma)
    with Not_found -> assert false in
  match lkrule with
  | Lltolj.SCaxiom (e) ->
    trhyp e
  | Lltolj.SCfalse ->
    Dk.dkapp2 (trhyp efalse) (trexpr goal)
  | Lltolj.SCtrue ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype (Dk.dklam dkvar (Dk.dkprf dkprop) dkvar)
  | Lltolj.SCeqref (a) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    Dk.dklam dkprop (Dk.dkarrow Dk.dktermtype Dk.dkproptype)
      (trproof (
	Lltolj.scrimply (
	  eapp (prop, [a]),
	  eapp (prop, [a]),
	  Lltolj.scaxiom (eapp (prop, [a]), [])),
	eimply (eapp (prop, [a]), eapp (prop, [a])), gamma))
  | Lltolj.SCeqsym (a, b) ->
    let term = new_term () in
    let dkterm = Dk.dkvar term in
    Dk.dkapp3 (trhyp (eapp ("=", [a; b])))
      (Dk.dklam dkterm Dk.dktermtype (trexpr (eapp ("=", [evar term; a]))))
      (trproof (Lltolj.sceqref (a, []), eapp ("=", [a; a]), gamma))
  | Lltolj.SCcut (e, lkrule1, lkrule2) ->
    trproof
      (lkrule2, goal,
       (e, trproof (lkrule1, e, gamma)) :: gamma)
  | Lltolj.SCland (e1, e2, lkrule) ->
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dkapp3 (trhyp (eand (e1, e2)))
      (trexpr goal)
      (Dk.dklam dkvar1
	 (Dk.dkprf (trexpr e1))
	 (Dk.dklam dkvar2
	    (Dk.dkprf (trexpr e2))
	    (trproof (lkrule, goal, (e1, dkvar1) :: (e2, dkvar2) :: gamma))))
  | Lltolj.SClor (e1, e2, lkrule1, lkrule2) ->
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
      Dk.dkapp (trhyp (eor (e1, e2)))
      [trexpr goal;
       Dk.dklam dkvar1
	 (Dk.dkprf (trexpr e1))
	 (trproof (lkrule1, goal, (e1, (Dk.dkvar var1)) :: gamma));
       Dk.dklam dkvar2
	 (Dk.dkprf (trexpr e2))
	 (trproof (lkrule2, goal, (e2, (Dk.dkvar var2)) :: gamma))]
  | Lltolj.SClimply (e1, e2, lkrule1, lkrule2) ->
    let traux =
      Dk.dkapp2 (trhyp (eimply (e1, e2))) (trproof (lkrule1, e1, gamma)) in
      trproof (lkrule2, goal, (e2, traux) :: gamma)
  | Lltolj.SClnot (e, lkrule) ->
    Dk.dkapp2 (trhyp (enot e)) (trproof (lkrule, e, gamma))
  | Lltolj.SClall (Eall (x, ty, p, _) as ap, t, lkrule) ->
    let traux =
      Dk.dkapp2 (trhyp ap) (trexpr t) in
      trproof
      (lkrule, goal, (substitute [(x, t)] p, traux) :: gamma)
  | Lltolj.SClex (Eex (x, ty, p, _) as ep, v, lkrule) ->
    let q = substitute [(x, v)] p in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dkapp3 (trhyp ep)
      (trexpr goal)
      (Dk.dklam (trexpr v) Dk.dktermtype
	 (Dk.dklam dkvar
	    (Dk.dkprf (trexpr q))
	    (trproof  (lkrule, goal, (q,dkvar) :: gamma))))
  | Lltolj.SCrand (e1, e2, lkrule1, lkrule2) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype
       (Dk.dklam dkvar
	  (Dk.dkarrow (Dk.dkprf (trexpr e1))
	     (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop)))
	  (Dk.dkapp3 dkvar (trproof (lkrule1, e1, gamma)) (trproof (lkrule2, e2, gamma))))
  | Lltolj.SCrorl (e1, e2, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar1
	 (Dk.dkarrow (Dk.dkprf (trexpr e1)) (Dk.dkprf dkprop))
	 (Dk.dklam dkvar2
	    (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop))
	    (Dk.dkapp2 dkvar1 (trproof (lkrule, e1, gamma)))))
  | Lltolj.SCrorr (e1, e2, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var1 = new_hypo () in
    let dkvar1 = Dk.dkvar var1 in
    let var2 = new_hypo () in
    let dkvar2 = Dk.dkvar var2 in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar1
	 (Dk.dkarrow (Dk.dkprf (trexpr e1)) (Dk.dkprf dkprop))
	 (Dk.dklam dkvar2
	    (Dk.dkarrow (Dk.dkprf (trexpr e2)) (Dk.dkprf dkprop))
	    (Dk.dkapp2 dkvar2 (trproof (lkrule, e2, gamma)))))
  | Lltolj.SCrimply (e1, e2, lkrule) ->
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkvar (Dk.dkprf (trexpr e1))
      (trproof (lkrule, e2, (e1, dkvar) :: gamma))
  | Lltolj.SCrnot (e, lkrule) ->
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkvar (Dk.dkprf (trexpr e))
      (trproof (lkrule, efalse, (e, dkvar) :: gamma))
  | Lltolj.SCrall (Eall (x, ty, p, _), v, lkrule) ->
    let q = substitute [(x, v)] p in
    Dk.dklam (trexpr v) Dk.dktermtype
      (trproof (lkrule, q, gamma))
  | Lltolj.SCrex (Eex (x, ty, p, _), t, lkrule) ->
    let prop = new_prop () in
    let dkprop = Dk.dkvar prop in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    Dk.dklam dkprop Dk.dkproptype
      (Dk.dklam dkvar
	 (Dk.dkpi (trexpr x) (Dk.dktermtype)
	    (Dk.dkarrow (Dk.dkprf (trexpr p)) (Dk.dkprf dkprop)))
	 (Dk.dkapp3 dkvar (trexpr t) (trproof (lkrule, substitute [(x, t)] p, gamma))))
  | Lltolj.SCcnot (e, lkrule) -> assert false
  | Lltolj.SClcontr (e, lkrule) ->
      trproof (lkrule, goal, gamma)
  | Lltolj.SCrweak (e, lkrule) ->
    Dk.dkapp2 (trproof (lkrule, efalse, gamma)) (trexpr e)
  | Lltolj.SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let pred = new_prop () in
    let dkpred = Dk.dkvar pred in
    let var = new_hypo () in
    let dkvar = Dk.dkvar var in
    let rec itereq (xts, ts, us) =
      match ts, us with
      | [], [] -> Dk.dkvar var
      | t :: ts, u :: us ->
	let term = new_term () in
	let dkterm = Dk.dkvar term in
	Dk.dkapp3 (trhyp (eapp ("=", [t; u])))
	  (Dk.dklam dkterm Dk.dktermtype
	     (trexpr (eapp (pred, [eapp (p, xts @ ((evar term) :: us))]))))
	  (itereq ((xts@[t]), ts, us))
      | _ -> assert false in
    Dk.dklam dkpred (Dk.dkarrow Dk.dktermtype Dk.dkproptype)
      (Dk.dklam dkvar (Dk.dkprf (trexpr (eapp (pred, [eapp (p, ts)]))))
	 (itereq ([], ts, us)))
  | Lltolj.SCeqprop (Eapp (p, ts, _), Eapp (_, us, _)) ->
    let rec itereq (xts, ts, us) =
      match ts, us with
      | [], [] -> trhyp (eapp (p, xts))
      | t :: ts, u :: us ->
	let term = new_term () in
	let dkterm = Dk.dkvar term in
	Dk.dkapp3 (trhyp (eapp ("=", [t; u])))
	  (Dk.dklam dkterm Dk.dktermtype ((trexpr (eapp (p, xts @ ((evar term) :: us))))))
	  (itereq ((xts@[t]), ts, us))
      | _ -> assert false;
    in
    itereq ([], ts, us)
  | _ -> assert false
