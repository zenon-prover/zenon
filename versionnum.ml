(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.86 2012-02-24 14:31:28 doligez Exp $";;

open Printf;;

let number = 241;;      (* strictly increasing *)
let date = "2012-02-24";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
