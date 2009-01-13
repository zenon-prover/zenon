(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.24 2009-01-13 16:20:53 doligez Exp $";;

open Printf;;

let number = 139;;      (* strictly increasing *)
let date = "2009-01-13";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
