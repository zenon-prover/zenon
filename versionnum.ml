(*  Copyright 2008 INRIA  *)
Version.add "$Id: 4b5a15ddd9e231963a758c70d3ad975691f4bd44 $";;

open Printf;;

let number = 253;;      (* strictly increasing *)
let date = "2013-03-04";;

let major = 0;;
let minor = 7;;
let bugfix = 2;;

let short = sprintf "%d.%d.%d" major minor bugfix;;
let full = sprintf "%d.%d.%d [a%d] %s" major minor bugfix number date;;
