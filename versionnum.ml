(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.48 2009-07-16 12:06:34 doligez Exp $";;

open Printf;;

let number = 176;;      (* strictly increasing *)
let date = "2009-07-11";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
