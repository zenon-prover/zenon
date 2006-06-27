(*  Copyright 2004 INRIA  *)
let myvers = "$Id: version.ml,v 1.42 2006-06-27 15:33:10 doligez Exp $";;

open Printf;;

let number = 54;;      (* strictly increasing *)
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
