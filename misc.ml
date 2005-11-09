(*  Copyright 2003 INRIA  *)
Version.add "$Id: misc.ml,v 1.5 2005-11-09 15:18:24 doligez Exp $";;


(* functions missing from the standard library *)

let rec index n e = function
  | [] -> raise Not_found
  | h :: _ when h = e -> n
  | _ :: t -> index (n+1) e t
;;

let ( @@ ) = List.rev_append;;

exception False;;
exception True;;

let occurs sub str =
  let lsub = String.length sub in
  let lstr = String.length str in
  try
    for i = 0 to lstr - lsub do
      try
        for j = 0 to lsub - 1 do
          if str.[i+j] <> sub.[j] then raise False;
        done;
        raise True;
      with False -> ()
    done;
    false
  with True -> true
;;

let rec xlist_init l f accu =
  if l = 0 then accu else xlist_init (l-1) f (f() :: accu)
;;

let list_init l f = xlist_init l f [];;

let isalnum c =
  match c with
  | 'A'..'Z' | 'a'..'z' | '0'..'9' -> true
  | _ -> false
;;

let rec list_last l =
  match l with
  | [] -> raise Not_found
  | [x] -> x
  | h::t -> list_last t
;;
