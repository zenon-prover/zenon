(*  Copyright 2003 INRIA  *)
Version.add "$Id: misc.ml,v 1.3 2004-09-09 15:25:35 doligez Exp $";;


(* functions missing from the standard library *)

let rec index n e = function
  | [] -> raise Not_found
  | h :: _ when h = e -> n
  | _ :: t -> index (n+1) e t
;;

let ( @@ ) = List.rev_append;;
