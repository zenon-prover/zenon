(*  Copyright 2004 INRIA  *)
Misc.version "$Id: eqrel.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

open Expr;;

let rec conjuncts accu e =
  match e with
  | Evar _
  | Emeta _
  | Eapp _
  | Etrue
  | Efalse
  | Eall _
  | Eex _
  | Etau _
    -> e :: accu
  | Enot (f, _) -> neg_conjuncts accu f
  | Eand (f1, f2, _) -> conjuncts (conjuncts accu f1) f2
  | Eor _
  | Eimply _
  | Eequiv _
    -> e :: accu

and neg_conjuncts accu e =
  match e with
  | Evar _
  | Emeta _
  | Eapp _
  | Etrue
  | Efalse
  | Eall _
  | Eex _
  | Etau _
    -> (enot e) :: accu
  | Enot (f, _) -> conjuncts accu f
  | Eor (f1, f2, _) -> neg_conjuncts (neg_conjuncts accu f1) f2
  | Eimply (f1, f2, _) -> neg_conjuncts (conjuncts accu f1) f2
  | Eand _
  | Eequiv _
    -> (enot e) :: accu
;;

let check_sym s s1 =
  match !s with
  | None -> s := s1; true
  | Some ss -> ss = s1
;;

let check_arg vars arg =
  match arg with
  | Evar (v, _) -> List.mem v vars
  | _ -> false
;;

let rec check_r s vars e =
  match e with
  | Evar _
  | Emeta _
  | Eall _
  | Eex _
  | Etau _
    -> false
  | Eapp (s1, args, _) -> check_sym s s1 && List.forall (check_arg vars) args
  | Enot (f, _) -> check_r s vars f
  | Eand (f1, f2, _) -> check_r s vars f1 && check_r s vars f2
  | Eor (f1, f2, _) -> check_r s vars f1 && check_r s vars f2
  | Eimply (f1, f2, _) -> check_r s vars f1 && check_r s vars f2
  | Eequiv (f1, f2, _) -> check_r s vars f1 && check_r s vars f2
  | Etrue
  | Efalse
    -> true
;;

exception Wrong_form;;

let rec atoms rs vars neg accu e =
  match e with
  | Evar _
  | Emeta _
  | Eall _
  | Eex _
  | Etau _
    -> raise Wrong_form
  | Eapp (s, args, _)
    when check_sym rs s && List.forall (check_arg vars) args ->
      (if neg then enot e else e) :: accu
  | Eapp _ -> raise Wrong_form
  | Enot (f, _) -> atoms rs vars (not neg) accu f
  | Eand (f1, f2, _) ->
      let a1 = atoms rs vars neg accu f1 in
      atoms rs vars neg a1 f2
  | Eor (f1, f2, _) ->
      let a1 = atoms rs vars neg accu f1 in
      atoms rs vars neg a1 f2
  | Eimply (f1, f2, _) ->
      let a1 = atoms rs vars (not neg) accu f1 in
      atoms rs vars neg a1 f2
  | Eequiv (f1, f2, _) ->


let filter_hyps l =
  
