(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.82 2010-06-17 10:43:22 doligez Exp $";;

open Printf;;

let number = 232;;      (* strictly increasing *)
let date = "2010-06-17";;

let major = 0;;
let minor = 7;;
let bugfix = 0;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
