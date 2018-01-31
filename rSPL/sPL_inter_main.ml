#include "xdebug.cppo"
(* PLEASE DO NOT CHANGE THIS FILE *)

open Debug
open SPL
open SPLc
open SPL_parser
open SPL_type
open SPL_inter


let parse_file (filename:string) : (string * SPL.sPL_expr) =
    SPL_parser.parse_file filename

(* main program *)
let main =
  if String.length !VarGen.file == 0 then print_endline VarGen.usage else 
    let _ = print_endline "LOADING sPL program .." in
    let _ = print_endline ("") in 
    let (s,p) = parse_file !VarGen.file in
    (*let _ = print_endline ("  "^s) in
    let _ = print_endline (" AS ==> "^(SPL.string_of_sPL p)) in*)
    let _ = print_endline "TYPE CHECKING program .." in
    let _ = print_endline ("") in 
    let (v,np) = SPL_type.type_infer_x [] p in
    match v with
      | None -> print_endline " ==> type error detected"
      | Some t ->
          let _ = print_endline (" ==> inferred type "^(SPL.string_of_sPL_type t)) in
          let _ = print_endline ("") in 
          (*let _ = print_endline ("TRANSFORMING TO CORE LANGUAGE ... ") in*)
          (* translate program into core sPL form to remove the let syntactic sugar *)
          let npc = SPL_type.trans_exp np in
          let _ = print_endline ("EVALUATING ... ") in
          let _ = print_endline ("") in
          let r = SPL_inter.evaluate npc in
          let r_string = SPLc.string_of_sPL r in 
          if (r_string = "DP")
          then print_endline("")
          else if (r_string = "ER") 
          then print_endline (" No tuples satisfied the conditions. ") 
          else print_endline (SPLc.string_of_sPL r)
      (*
            begin
              print_endline (" ==> inferred type "^(S.string_of_sPL_type t));
              let _ = print_string "TRANSFORMING ==> " in
              let np = trans_exp np in
              let _ = print_endline (string_of_sPL np) in
              ()
            end
        *)
