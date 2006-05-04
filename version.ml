(*  Copyright 2004 INRIA  *)
let myvers = "$Id: version.ml,v 1.40 2006-05-04 16:51:39 doligez Exp $";;

open Printf;;

let number = 50;;      (* strictly increasing *)
let date = "2006-05-04";;

let major = 0;;
let minor = 4;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [%d] %s" major minor bugfix number date;;


(* CVS version strings *)

let version_list = ref [myvers];;

let add x = (version_list := x :: !version_list);;

let print_cvs ch = List.iter (fun x -> fprintf ch "%s\n" x) !version_list;;
