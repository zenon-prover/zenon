(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.77 2010-04-23 22:14:47 doligez Exp $";;

open Printf;;

let number = 226;;      (* strictly increasing *)
let date = "2010-04-23";;

let major = 0;;
let minor = 6;;
let bugfix = 4;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
