(*  Copyright 2008 INRIA  *)
Version.add "$Id: versionnum.ml,v 1.76 2010-04-23 11:32:45 doligez Exp $";;

open Printf;;

let number = 225;;      (* strictly increasing *)
let date = "2010-04-22";;

let major = 0;;
let minor = 6;;
let bugfix = 4;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
