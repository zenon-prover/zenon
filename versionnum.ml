(*  Copyright 2008 INRIA  *)
let myvers = "$Id: versionnum.ml,v 1.3 2008-10-23 16:08:52 doligez Exp $";;

open Printf;;

let number = 97;;      (* strictly increasing *)
let date = "2008-10-23";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
