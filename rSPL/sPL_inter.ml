open SPL 
open SPLc

exception Dummy_Exception
let selection_predicate op e1 e2 = 
  if (op = "<=") then (e1 <= e2)
  else if (op = ">=") then (e1 >= e2)
  else if (op =  "<")  then (e1 < e2)
  else if (op =  ">")  then (e1 > e2) 
  else if (op =  "=")  then (e1 = e2)
  else if (op = "!=") then (not (e1 = e2))
  else raise (Dummy_Exception) (* This case will not occur since we 
  have ensured that the correct symbols are entered*)

(* Look up the correspoding value for a given variable
  el in the environment env. *)
let rec env_lookup el env = 
  match env with 
    | [] -> None
    | (id , value) :: t -> 
       if el = id 
       then Some value 
       else env_lookup el t

(* This function takes an expression and an environment, and substitutes 
the variables in the expression based on the environment provided. *)
let rec substitute (exp: sPL_expr) (env: (id * sPL_expr) list):sPL_expr = 
  match exp with 
    | Var x -> 
        begin
          match (env_lookup x env) with 
          | Some value -> value
          (*| None -> this situation will never occur because our type inference
           and let expression transformation are sound. *)
        end 
    | Projection (rel , tg , t ) ->
        Projection ((substitute rel env) , tg , t)
    | Join (r1 , r2 , t) ->
        Join ( (substitute r1 env) , (substitute r2 env) , t)
    | Selection1 (rel_exp , id1 , op , id2) -> 
        Selection1 ((substitute rel_exp env) , id1 , op , id2)
    | Selection2 (rel_exp , id1 , op , value) -> 
        Selection2 ((substitute rel_exp env) , id1 , op , value)



(* use primitive rule to contract op[v1,v2] or op[v] to a value *)
(* raise an exception if we cannot directly contract *)
let rec contract (e:sPL_expr): sPL_expr = 
  (* Reduces arithmetic/boolean expressions in relations. *)
  match e with
    | Projection (relation , tags , Some ty) ->
        begin
          let Relation (rel_type , row_lst) = relation 
          in
          let RelationType ( _ , tag_type_lst) = rel_type
          in
          let new_row_lst = 
          (* row_lst and tag_type_lst are of the same length *)
          List.fold_right
          (
            (* Fold through the list of lists, take each 
              element (representing a row), and remove 
              the column elements of that row not present 
              in the tag list. *)
            fun a b ->
             (    
                (* fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c *)
                (* Check if the tag for a given column is
                present in the tags list. If this is the case, 
                append the column value to the row, else don't. *)
                List.fold_right2
                  (
                    fun x y z ->
                      let ( id , _ ) = y
                      in 
                      if (List.mem id tags) 
                      then x::z
                      else z  
                  )
                a
                tag_type_lst
                []
              )::b
          )
          row_lst
          []
        in
        (* We use the type inferred in the type inference stage. *)
        (Relation (ty , new_row_lst))
        end

    | Join (rel1 , rel2 , Some ty) -> 
        begin
          let Relation (RelationType (rel_name1 , l1) , lol1) = rel1
          and Relation (RelationType (rel_name2 , l2) , lol2) = rel2
          in
          (* Obtain common tag_id pairs. *)
          let common = 
           List.fold_right
           (
            fun a b ->
             if (List.mem a l2) 
             then a::b
             else b 
           ) l1 []
          in
          let lol_new = 
          (* Iterate through the first relation.*)
          List.fold_right
          (
            fun a b ->
               let comb1 = List.combine a l1 
               in 
               (* Iterate through second relation. *)
                  (
                   List.fold_right 
                   (
                     fun x y -> 
                     let comb2 = List.combine x l2 
                     in 
                     (* For each elements of each row of the second relation, 
                     check whether it is present in the corresponding row of 
                     the first relation. If so, increase a counter. Check if 
                     the counter is equal to the number of common columns 
                     earlier computed. *)
                     if (List.length common =
                       List.fold_right
                       (
                         fun f g -> 
                           if List.mem f comb1 
                           then (g+1) 
                           else g
                       )
                       comb2
                       0)
                     (* If this is the case, filter
                     the second list of the basis of the common tabs and attach it to the first row.
                     This enables multiple usage of rows in the first relation. *)
                     then 
                       let joined_row = a @  
                       List.map
                       (fun (var , _ ) -> var)
                       (
                         List.filter 
                         (
                           fun (_ , tag_ty_pair) -> 
                             Pervasives.not (List.mem tag_ty_pair common)
                         ) 
                         comb2
                       )
                       in
                       joined_row :: y

                     else y
                   )
                   lol2
                   []
                 ) @ b
          )    
          lol1
          []
          in 
          (Relation (ty , lol_new)) 
        end
    | Selection1 (rel , id1 , op , id2) -> 
        let Relation (RelationType (rel_name , tag_ty_pair) , lol) = rel 
        in
        let new_lol = 
        (* Fold across the list of tuples *)
        List.fold_right 
        (
          fun a b -> 
          (* For each tuple, combine the elements with the corresponding tag_type values.
          Then filter the list to retain only those tags that are required in the
          selection. *)
            let comb = List.combine tag_ty_pair a 
            in
            let [(_ , v1)] = 
            List.filter 
            (
              fun ( (tag , _ ) , _) ->
                 tag = id1 
            )
            comb
            and  [(_ , v2)] = 
            List.filter 
            (
              fun ( (tag , _ ) , _) ->
                 tag = id2 
            )
            comb
            in 
            (* Finally check if the predicate is met. If this is the case,
            attach the tuple to the new list. If not, continue. *)
            if (selection_predicate op v1 v2)
            then a::b
            else b
        )
        lol
        []
        in
        (Relation (RelationType (rel_name , tag_ty_pair)  , new_lol))

    | Selection2 (rel , id1 , op , value) -> 
        let Relation (RelationType (rel_name , tag_ty_pair) , lol) = rel 
        in
        let new_lol = 
        (* Fold across the list of tuples *)
        List.fold_right 
        (
          fun a b -> 
          (* For each tuple, combine the elements with the corresponding tag_type values.
          Then filter the list to retain only those tags that are required in the
          selection. *)
            let comb = List.combine tag_ty_pair a 
            in
            let [(_ , v1)] = 
            List.filter 
            (
              fun ( (tag , _ ) , var) ->
                 tag = id1 
            )
            comb
            in 
            (* Finally check if the predicate is met. If this is the case,
            attach the tuple to the new list. If not, continue. *)
            if (selection_predicate op v1 value)
            then a::b
            else b
        )
        lol
        []
        in
        (Relation (RelationType (rel_name , tag_ty_pair)  , new_lol))
    | BoolConst _ | IntConst _ -> e    
    | UnaryPrimApp (op,arg) ->
        begin
          match op with
            | "~" ->
                begin
                  match arg with
                    | IntConst v -> IntConst (-v)
                    | _ -> failwith ("unable to contract for "^(string_of_sPL e))
                end
            | "\\" ->
                (* please complete *)
                begin
                  match arg with
                    |BoolConst v -> 
                        begin
                          match v with
                            |true -> BoolConst (false)
                            |false -> BoolConst (true) 
                        end
                    | _ -> failwith ("unable to contract for "^(string_of_sPL e))
                end
            | _ -> failwith ("illegal unary op "^op)
        end
    | BinaryPrimApp (op,arg1,arg2) ->
        begin
          match op with
            | "+" ->
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1+v2)
                    | _,_ -> failwith ("unable to contract "^(string_of_sPL e))
                end
            | "-" ->
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1-v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "*" ->
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1*v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "/" ->
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1/v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "|" ->
                begin
                  (* please complete *)
                  match arg1,arg2 with
                    |BoolConst v1, BoolConst v2 -> 
                        if (v1 = false && v2 = false) then BoolConst (false)
                        else BoolConst(true)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "&" ->
                begin
                  (* please complete *)
                  match arg1,arg2 with
                    |BoolConst v1, BoolConst v2 -> 
                        if (v1 = true && v2 = true ) then BoolConst (true)
                        else BoolConst(false)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "<" ->
                (* please complete *)
                begin
                  match arg1,arg2 with
                    |IntConst v1, IntConst v2 -> BoolConst (v1<v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | ">" ->
                (* please complete *)
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> BoolConst (v1>v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "=" ->
                (* please complete with bool case *)
                begin
                  match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> BoolConst (v1=v2)
                    | BoolConst v1, BoolConst v2 -> BoolConst (v1=v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            (* Contraction for exponentiation. Note that the other way in which exponentiation could have been implemented would involved instantiating a separate ePL_exp constructor, and then converting the arguments of the constructor into a recursive BinaryPrimApp structure using the '*' operator. *)
            | "^" ->
                begin
                  match arg1, arg2 with 
                    |IntConst v1,IntConst v2 -> 
                        begin
                          let rec exp x y =
                            if y = 0 then 1
                            else if (y mod 2 = 0) then (exp (x*x) (y/2))
                            else ( exp (x*x) (y/2)) * x 
                          in 
                            if (v2 < 0) (* Since ePL only allows integers as expressions, negative exponenets (which will lead to floating point values), are evaluated to 0. *)
                            then IntConst (0)
                            else IntConst (exp v1 v2)

                        end

                    |_,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | _ -> failwith ("illegal binary op "^op)
        end

(* Check if a relation is reducible or not. *)
let reduce_relation rel = 
    let Relation (rel_type , lol) = rel 
    in 
    not (
    List.for_all
    (
      fun a -> 
        (* All values must be either ints or bools *)
        List.for_all
        (fun x -> 
           match x with 
             |IntConst _ | BoolConst _ -> true
             | _ -> false
        )
        a
    )
    lol
    )

(* check if an expression is reducible or irreducible *)
let reducible (e:sPL_expr) : bool = 
  match e with
    | BoolConst _ | IntConst _ -> false
    | UnaryPrimApp _ | BinaryPrimApp _ -> true
    (* Adding a reducible the Relational Database operation constructors. *)
    | Relation _ -> reduce_relation (e)
    | Projection _ | Join _ | Selection1 _ | Selection2 _ -> true 

(* if expr is irreducible, returns it *)
(* otherwise, perform a one-step reduction *)
let rec oneStep (e:sPL_expr): sPL_expr = 
  match e with
    | BoolConst _ | IntConst _ ->  e
    | UnaryPrimApp (op,arg) ->
        if reducible arg then UnaryPrimApp(op,oneStep arg)
        else contract e
    | BinaryPrimApp (op,arg1,arg2) -> 
        if reducible arg1 
        then BinaryPrimApp(op,oneStep arg1,arg2)
        else 
        if reducible arg2
        then BinaryPrimApp(op,arg1,oneStep arg2)
        else contract e
    (* One step evaluation for relational databases. *)
    | Relation (rel_type , lol) -> 
        let new_lol = 
        List.fold_right
        (
          fun a b ->
          (
             List.fold_right 
             (
                fun x y ->
                (
                  oneStep x
                )::y
             )
             a
             []
          ) :: b
        )
        lol
        [] 
        in
        Relation (rel_type , new_lol)
        
    | Projection (rel_exp , tags , ty) -> 
      if reducible rel_exp
      then Projection (oneStep rel_exp , tags , ty) 
      else contract e
    | Join (rel_exp1 , rel_exp2 , ty) ->
      if reducible rel_exp1
      then  Join (oneStep rel_exp1 , rel_exp2 , ty)
      else 
      if reducible rel_exp2
      then  Join (rel_exp1 , oneStep rel_exp2 , ty)
      else contract e 
    | Selection1 (rel_exp1 , id1 , op , id2) -> 
      if reducible rel_exp1
      then Selection1 (oneStep rel_exp1 , id1 , op , id2)
      else contract e 
    | Selection2 (rel_exp1 , id1 , op , value) -> 
      if reducible rel_exp1
      then Selection2 (oneStep rel_exp1 , id1 , op , value)
      else contract e 

    (* Etc. We may add more expressions to extend the scope of our DSL*)


(* keep reducing until we get a irreducible expr *)
(* or has an exception due to wrong operator or type error *)
let rec evaluate (e:sPL_expr): sPL_expr = 
  match e with 
    | Appln (func , ty , real_params) -> 
        begin
          let Func ( _ , formal_params , body) = func 
          in
          let env = (List.combine formal_params real_params)
          in
          (* We subsitute the formal parameters with
          the real parameters. This leaves us with an evaluable 
          expression. Note that this strategy will only work
          for complete function application.  *)
          let exp = substitute body env 
          in
          if (reducible exp) then evaluate (oneStep exp)
          else exp
        end
    | _ ->
        if (reducible e)
        then evaluate (oneStep e)
        else e



(* sample expr in AST form *)
let e1 = IntConst 42
let e2 = 
  BinaryPrimApp ("+",
                 BinaryPrimApp("*",
                               UnaryPrimApp("~",IntConst 15),
                               IntConst 7),
                 IntConst 2)
let e2a = 
  BinaryPrimApp (">",IntConst 7,IntConst 10)
let e2b = 
  BinaryPrimApp ("=",
                 IntConst 10,
                 BinaryPrimApp("+",IntConst 3,IntConst 7))

let e3 = 
  BinaryPrimApp ("|",
                 BinaryPrimApp("&",
                               UnaryPrimApp("\\",BoolConst false),
                               BoolConst true),
                 BoolConst true)
let e4 = 
  BinaryPrimApp ("+",IntConst 15,BoolConst true)
let e5 = 
  BinaryPrimApp ("!",IntConst 15,BoolConst true)
let e5 = 
  BinaryPrimApp (">",BoolConst false,BoolConst true)
let e6 = 
  BinaryPrimApp ("*",
                 BinaryPrimApp ("+",IntConst 1,IntConst 2),
                 IntConst 3)
let e7 = 
  BinaryPrimApp ("+",
                 IntConst 1,
                 BinaryPrimApp ("*",IntConst 2,IntConst 3))

