(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.74 2010-04-01 13:08:57 doligez Exp $";;

open Printf;;

let number = 218;;      (* strictly increasing *)
let date = "2010-04-01";;

let major = 0;;
let minor = 6;;
let bugfix = 4;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
