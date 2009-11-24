(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.65 2009-11-24 15:08:01 doligez Exp $";;

open Printf;;

let number = 208;;      (* strictly increasing *)
let date = "2009-11-24";;

let major = 0;;
let minor = 6;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
