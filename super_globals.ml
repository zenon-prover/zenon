(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
Version.add "$Id$";;

let time_limit_init = ref 300.;;
let time_limit_super () = 
  !time_limit_init*.4./.5.;;

let progress_period = ref 100;;
let progress_counter = ref !progress_period;;
let progress_last = ref 0.0;;
let period_base = 0.3;;
