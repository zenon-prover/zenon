(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.39 2009-06-04 15:36:46 doligez Exp $";;

open Printf;;

let number = 162;;      (* strictly increasing *)
let date = "2009-06-04";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
