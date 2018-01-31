(* PLEASE DO NOT CHANGE THIS FILE *)

module S = SPL

type op_id = S.op_id
type id = S.id
type sPL_type = S.sPL_type

(* open Gen *)
open Debug


(* AST for core language *)
type sPL_expr =
  | BoolConst of bool
  | IntConst of int
  | Var of id
  | UnaryPrimApp of op_id * sPL_expr
  | BinaryPrimApp of op_id * sPL_expr * sPL_expr
  | Cond of sPL_expr * sPL_expr * sPL_expr
  | Func of sPL_type * (id list) * sPL_expr 
        (* min of one parameter *)
  | RecFunc of sPL_type * id * (id list) * sPL_expr 
        (* min of one parameter *)
  | Appln of sPL_expr * sPL_type * (sPL_expr list) 
        (* all applications fully applied *)
  | Relation of (sPL_type * (sPL_expr list) list)
  | Projection of (sPL_expr * id list * sPL_type option)
  | Join of (sPL_expr * sPL_expr * sPL_type option)
  | Selection1 of (sPL_expr * id * op_id * id)
  | Selection2 of (sPL_expr * id * op_id * sPL_expr)
 

(* display sPL expr in prefix form *)
(* PLEASE do not change *)
let string_of_sPL (e:sPL_expr):string =
  let pr_type t = "{"^(S.string_of_sPL_type t)^"}" in
  let rec aux e =
  match e with
    | BoolConst v -> (string_of_bool v) (*"Bool("^(string_of_bool v)^")"*)
    | IntConst v -> (string_of_int v) (*"Int("^(string_of_int v)^")"*)
    | Var v -> "Var("^v^")"
    | UnaryPrimApp (op,arg) -> op^"["^(aux arg)^"]"
    | BinaryPrimApp (op,arg1,arg2) -> op^"["^(aux arg1)^","^(aux arg2)^"]"
    | Cond (e1,e2,e3) -> "if "^(aux e1)^" then "^(aux e2)^" else "^(aux e3)
    | Func (t,args,body) -> "fun "^(pr_type t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | RecFunc (t,r,args,body) -> "recfun "^r^" "^(pr_type t)^" "^(pr_lst " " pr_id args)^" -> "^(aux body)^" end"
    | Appln (e,t,args) -> "Appln["^(aux e)^"; "^(pr_lst ";" aux args)^"]"

    | Relation (t , lol) ->
        begin 
          let type_representation = pr_type t in
          let S.RelationType (_ , tag_ty_lst) = t in
          let tags = "| "^List.fold_right (fun (tag , _) b -> tag^" | "^b) tag_ty_lst "" in 
          let lol_rep = 
          List.fold_right
          (
            fun a b ->
              let temp =  
              (
                List.fold_right 
                (
                  fun c d ->
                    (aux c) ^ "   ;   " ^ d
                )
                a
                ""
              )
             in ("[ "^(String.sub temp 0 ((String.length temp) - 4))^ "] ") :: b
          )
          lol
          []
          in  
          let _ = print_endline ("The resulting Relation is as follows: ") in
          let _ = print_endline ("") 
          in
          let _ = print_endline ("Relation Type: "^type_representation)
          in 
          let _ = print_endline ("")
          in
          let _ = print_endline ("Relation: ")
          in
          let _ = print_endline ("")
          in
          let _ = print_endline tags 
          in
          let rv = 
             if (List.length lol_rep > 0 )
             then 
                let _ =
                 List.map 
                 (fun a -> print_endline a)
                 lol_rep
                in "DP" (* DP: Don't print anything *)
             else 
                "ER" (* Empty Relation *)
          in rv

          
        end 
    (* Projection, Join, and Selection cases are never required since Rel_Al always contracts to a Relation*)
    | Projection (rel , tag_lst , _) -> 
        let relation_rep = aux rel in
        let temp = 
         (
          List.fold_right 
                (
                  fun tag d ->
                    tag ^ " ;" ^ d
                )
                tag_lst
                ""
          )
        in 
         "Projection" ^ "( " ^ relation_rep ^ ", [ "^(String.sub temp 0 ((String.length temp) - 2))^ "]" ^ " )"

    | Join (rel1 , rel2 , Some _) -> 
         (aux rel1) ^ " |><| " ^ (aux rel2)

  in aux e


(* free vars of an expression *)
let rec fv (e:sPL_expr) : id list =
  match e with
    | BoolConst _  | IntConst _ -> []
    | Var i -> [i]
    | UnaryPrimApp (_,arg) -> fv arg
    | BinaryPrimApp (_,arg1,arg2) -> (fv arg1)@(fv arg2)
    | Cond (e1,e2,e3) -> (fv e1)@(fv e2)@(fv e3)
    | Func (_,vs,body) -> diff (fv body) vs
    | RecFunc (_,i,vs,body) -> diff (fv body) (i::vs)
    | Appln (e1,_,es) -> (fv e1)@(List.concat (List.map fv es))


