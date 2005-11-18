(*  Copyright 2004 INRIA  *)
let myvers = "$Id: version.ml,v 1.27 2005-11-18 13:09:59 doligez Exp $";;

open Printf;;

let number = 34;;      (* strictly increasing *)
let date = "2005-11-17";;

let major = 0;;
let minor = 4;;
let bugfix = 0;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [%d] %s" major minor bugfix number date;;


(* CVS version strings *)

let version_list = ref [myvers];;

let add x = (version_list := x :: !version_list);;

let print_cvs ch = List.iter (fun x -> fprintf ch "%s\n" x) !version_list;;
