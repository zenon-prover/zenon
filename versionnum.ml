(*  Copyright 2008 INRIA  *)
let myvers = "$Id: versionnum.ml,v 1.6 2008-10-29 10:37:58 doligez Exp $";;

open Printf;;

let number = 103;;      (* strictly increasing *)
let date = "2008-10-28";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
