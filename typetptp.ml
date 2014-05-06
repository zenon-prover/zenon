
open Expr

type env = {
    dummy : int;
}

let empty_env = {
    dummy = 0;
}

let first_chars s n = String.sub s 0 n
let after_chars s n = String.sub s n (String.length s - n)

let is_typed s = (first_chars s 6) = "typed_"
let notype_kind s = after_chars s 6

let map_fold f s l =
    let e, env = List.fold_left (fun (acc, env) e -> let x, env = f env e in (x :: acc, env)) ([], s) l in
    List.rev e, env

let type_tff_expr env e = e, env

(* TODO: check that all variables have no type, i.e type Namespace.univ_name  *)
let rec type_fof_expr e = match e with
    | Evar _
    | Etrue
    | Efalse ->
            ()
    | Emeta (v, _) ->
            type_fof_expr v
    | Eapp (_, l, _) ->
            List.iter type_fof_expr l
    | Enot (e', _) ->
            type_fof_expr e'
    | Eand (e', e'', _)
    | Eor (e', e'', _)
    | Eimply (e', e'', _)
    | Eequiv (e', e'', _) ->
            type_fof_expr e';
            type_fof_expr e''
    | Eall (e', t, e'', _)
    | Eex (e', t, e'', _)
    | Etau (e', t, e'', _)
    | Elam (e', t, e'', _) ->
            if t <> Namespace.univ_name then
                Error.err "Typed variable in untyped formula.";
            type_fof_expr e';
            type_fof_expr e''

let type_phrase env p = match p with
    | Phrase.Formula (name, kind, e) ->
            if is_typed kind then
                let e', env' = type_tff_expr env e in
                Phrase.Formula (name, notype_kind kind, e'), env'
            else begin
                type_fof_expr e;
                p, env
            end
    | _ -> p, env

let typecheck x =
    let p, _ = map_fold type_phrase empty_env x in
    p

