(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.28 2009-02-13 14:55:50 doligez Exp $";;

open Printf;;

let number = 143;;      (* strictly increasing *)
let date = "2009-02-12";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
