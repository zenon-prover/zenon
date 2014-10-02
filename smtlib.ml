(* Copyright 2014 INRIA **)

open Expr
open Phrase
open Smtlib_syntax

exception Incomplete_translation

(* Misc functions *)
let rec flat_map f = function
    | [] -> []
    | x :: r -> begin match f x with
        | None -> flat_map f r
        | Some y -> y :: flat_map f r
    end

let opt = function
    | Some x -> x
    | None -> failwith "Expected a non-empty option"

let new_hyp_name =
    let i = ref 0 in
    let f () = incr i; "hyp" ^ (string_of_int !i) in
    f

(* Environment *)
type env = {
    defined_sorts : unit;
    defined_funs : unit;
}

(* Term translation *)
let translate_const = function
    | SpecConstsDec(_, s) -> Arith.mk_rat s
    | SpecConstNum(_, s) -> Arith.mk_int s
    | SpecConstString(_, s) -> eapp (estring, [evar s])
    | SpecConstsHex(_, s) -> Arith.mk_int ("0" ^ (String.sub s 1 (String.length s - 1)))
    | SpecConstsBinary(_, s) -> Arith.mk_int ("0" ^ (String.sub s 1 (String.length s - 1)))

let translate_symbol = function
    | Symbol(_, s) -> s
    | SymbolWithOr(_, s) -> s

let translate_id = function
    | IdSymbol(_, s) -> translate_symbol s
    | IdUnderscoreSymNum(_, s, n) -> raise Incomplete_translation

let rec translate_sort = function
    | SortIdentifier(_, id) -> Type.atomic (translate_id id)
    | SortIdSortMulti(_, f, (_, l)) -> Type.mk_constr (translate_id f) (List.map translate_sort l)

let translate_sortedvar = function
    | SortedVarSymSort(_, s, t) -> tvar (translate_symbol s) (translate_sort t)

let translate_qualid = function
    | QualIdentifierId(_, id) -> evar (translate_id id)
    | QualIdentifierAs(_, id, s) -> raise Incomplete_translation

let rec translate_term = function
    | TermSpecConst(_, const) -> translate_const const
    | TermQualIdentifier(_, id) -> translate_qualid id
    | TermQualIdTerm(_, f, (_, l)) ->
            eapp (translate_qualid f, List.map translate_term l)
    | TermForAllTerm(_, (_, l), t) ->
            let t' = translate_term t in
            List.fold_right (fun v t ->
                let v' = translate_sortedvar v in
                eall (v', opt @@ get_type v', t)) l t'
    | TermExistsTerm(_, (_, l), t) ->
            let t' = translate_term t in
            List.fold_right (fun v t ->
                let v' = translate_sortedvar v in
                eex (v', opt @@ get_type v', t)) l t'
    | _ -> raise Incomplete_translation

(* Command Translation *)
let translate_command = function
    | CommandDeclareSort(_, s, n) ->
            (* Delcare new type constructor with arity n (as string) *)
            None
    | CommandDefineSort(_, s, (_, l), t) ->
            (* Abbreviation with parameters l *)
            None
    | CommandDeclareFun(_, s, (_, args), ret) ->
            (* new function args type to ret type *)
            None
    | CommandDefineFun(_, s, (_, args), ret, t) ->
            (* abbreviations with arguments l, ret type and expression t *)
            None
    | CommandAssert(_, t) ->
            Some(Hyp (new_hyp_name (), translate_term t, 1))
    | _ -> None

let translate_commands = function
    | Commands(_, (_, l)) -> flat_map (fun c ->
            try
                translate_command c
            with Incomplete_translation ->
                Error.warn ("Incomplete translation of a command.");
                None) l

let translate = function
    | Some commands -> translate_commands commands
    | None -> []
