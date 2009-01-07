(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.22 2009-01-07 16:07:04 doligez Exp $";;

open Printf;;

let number = 137;;      (* strictly increasing *)
let date = "2009-01-07";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
