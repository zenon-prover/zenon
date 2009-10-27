(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.64 2009-10-27 14:08:36 doligez Exp $";;

open Printf;;

let number = 204;;      (* strictly increasing *)
let date = "2009-10-27";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;       (* even = development version; odd = released version *)

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
