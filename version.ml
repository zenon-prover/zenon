(*  Copyright 2004 INRIA  *)
let myvers = "$Id: version.ml,v 1.43 2006-06-29 08:32:15 doligez Exp $";;

open Printf;;

let number = 55;;      (* strictly increasing *)
let date = "2006-06-27";;

let major = 0;;
let minor = 5;;
let bugfix = 0;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [%d] %s" major minor bugfix number date;;


(* CVS version strings *)

let version_list = ref [myvers];;

let add x = (version_list := x :: !version_list);;

let print_cvs ch = List.iter (fun x -> fprintf ch "%s\n" x) !version_list;;
