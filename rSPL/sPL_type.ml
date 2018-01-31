(* Oishik Ganguly 

   Lab 06 *)

#include "xdebug.cppo"

open SPL
open Debug
(* open Gen *)

module C = SPLc

type env_type = sPL_type Environ.et
let tail_optimize_flag = ref false
let pa_removal_flag = ref true
let stack_size = ref 10000

let option_flag = [
  ("--tail", Arg.Set tail_optimize_flag, "Enable tail-call optimization.")
;("--dis-pa", Arg.Clear pa_removal_flag, "Disable partial application Removal.")
;("-stk-size", Arg.Set_int stack_size,
  "Size of Stack Memory (default is 10000)")
(* ;("-dre", Arg.String (fun s -> *)
(*     DebugCore.z_debug_file:=("$"^s); DebugCore.z_debug_flag:=true), *)
(*  "Shorthand for -debug-regexp") *)
]@command_args



   (* Function to take two lists and return their 
common elements. Assume that there are no duplicate
elements in either list. 
We first find all the common elements between l1
and l2. Then we remove the common elements in 
l2 (denoted right_lst). Finally, we concatenate 
l1 and right_lst. *)

let construct_join_type l1 l2 = 
  let common = 
   List.fold_right
   (
    fun a b ->
     if (List.mem a l2) 
     then a::b
     else b 
   )
   l1 
   []
   in let right_lst = 
   List.fold_right
   (
    fun a b ->
     if (List.mem a common) 
     then b
     else a::b
   )
   l2 
   []
   in (l1 @ right_lst)


let _ = Debug.parse option_flag 

(* if (v,r) in env, return Some r *)
(* otherwise, return None *)
let get_type env v = Environ.get_val env v

(* match a function type t with its parameters args *)
(* and return its residual *)
(* extr_arg_type (t1->t2->t3->t4) [e1,e2] 
   ==> Some ([(e1,t1);(e2,t2)], t3->t4) *)
(* match a function type t with its parameters args *)
(* and return its residual *)
(* extr_arg_type (t1->t2->t3->t4) [e1,e2] ==> Some ([(e1,t1);(e2,t2)], t3->t4) *)
(* use test harness below and run ./splt *)
let extr_arg_type (t:sPL_type) (args:'a list) : (('a * sPL_type) list * sPL_type) option =
  let rec aux env t args =
    match args,t with
      | [],_ -> Some (List.rev (env),t)
      | v::vs,Arrow (t1,t2) ->  aux ((v,t1)::env) t2 vs
      | _,_ -> None
  in aux [] t args

let extr_arg_type_test (t:sPL_type) (args:'a list) : (('a * sPL_type) list * sPL_type) option =
  let pr1 = string_of_sPL_type in
  let pr2 = pr_list string_of_int in
  let pr2a = pr_list (pr_pair string_of_int pr1) in
  let pr3 = pr_option (pr_pair pr2a pr1) in
    Debug.no_2 "extr_arg_type_test" pr1 pr2 pr3 extr_arg_type t args

let selection_op_id_lst = [">" ; "<" ; ">=" ; "<=" ; "=" ; "!="]


(* test harness below to debug extr_arg_type *)
(* please comment them after fixing bug *)
(* let () = y_binfo_pp "Testing extr_arg_type_test\n";; *)
let t1 = Arrow (IntType,IntType)
let _ = x_add extr_arg_type_test t1 [1]
let _ = x_add extr_arg_type_test t1 [1;2]
let _ = x_add extr_arg_type_test t1 [1;2;3]

(* type checking method *)
(* you may use this method to check that the your inferred *)
(* type is correct *)
let type_check (env:env_type) (e:sPL_expr) (t:sPL_type) : bool =
  let rec aux env e t =
    match e with
   (* Check whether inferred type matches annotated type *)
      | Relation (ty , expr_lst) -> 
          ( ty = t )
   (* Check whether inferred type has correct types for each tag. 
      Note that since we use the annotated type specification to obtain the tags
      in type inference for the original relation, we are guaranteed to have the correct tags.
      However, the types for each tags may be incorrectly inferred. We check for this *)
      | Projection ( relation , tag_lst , ty)  -> 
        begin
          match ty with
            | Some ty1 -> 
                let Relation ( RelationType (rel_name , rel_ty_lst) , _ ) = relation
                and RelationType (rel_name_proj , rel_ty_lst_proj) = ty1 
                in
                (* Check if the tag:type list elements for the projection are present in 
                 the relation tag:type list. *)
                ( 
                  List.for_all
                  (
                    fun a ->
                      List.mem a rel_ty_lst
                  )
                  rel_ty_lst_proj
                ) 
                &&
                (* Additionally, check if the name of the projected type if the name of the original relation
                with a "p" appended to it. *)
                (rel_name^"p" = rel_name_proj)
            | None -> failwith "missing type : should call type_infer first"
        end   
      | Join (rel1 , rel2 , ty) -> 
         begin 
          match ty with 
            | Some ty1 ->
              let RelationType (join_ty_name , join_ty_lst) = ty1
              and Relation (RelationType (rel1_ty_name , rel1_ty_lst) , _ ) = rel1
              and Relation (RelationType (rel2_ty_name , rel2_ty_lst) , _ ) = rel2
              in 
              (construct_join_type rel1_ty_lst rel2_ty_lst) = join_ty_lst
              &&
              (join_ty_name = rel1_ty_name ^ rel2_ty_name)
            | None -> failwith "missing type : should call type_infer first"
         end
      (* Since the inferred type is the type of the rel_exp, check its type. *)
      | Selection1 (rel_exp , id1 , op , id2) ->
          aux env rel_exp t
      | Selection2 (rel_exp , id1 , op , value) -> 
          aux env rel_exp t
      | IntConst _ -> 
          if t=IntType then true else false
      | BoolConst _ -> 
          if t=BoolType then true else false
      | Var v ->
          (match get_type env v with
            | Some t2 -> t=t2
            | None -> false (* failwith ("type-check : var "^v^" cannot be found") *)
          )
      | UnaryPrimApp (op,arg) ->
          begin
            match op,t with
              | "~",IntType 
                -> aux env arg IntType
              | "\\",BoolType 
                -> aux env arg BoolType
              | _,_ 
                -> false
          end
      | BinaryPrimApp (op,arg1,arg2) ->
          begin
            match op,t with
              | "+",IntType | "-",IntType | "*",IntType | "/",IntType 
                -> (aux env arg1 IntType) && (aux env arg2 IntType)
              | "<",BoolType | ">",BoolType | "=",BoolType 
                -> (aux env arg1 IntType) && (aux env arg2 IntType)
              | "|",BoolType | "&",BoolType 
                -> (aux env arg1 BoolType) && (aux env arg2 BoolType)
              | _,_ -> false
          end
      | Cond (e1,e2,e3) ->
          let b1 = aux env e1 BoolType in
          let b2 = aux env e2 t in
          let b3 = aux env e3 t in
            b1 && b2 && b3
      | Func (te,args,body) ->
          if te=t then
            match extr_arg_type te args with
              | Some (env2,t2) -> aux (env2@env) body t2
              | None -> false (* mismatch in number of arguments *)
          else false
      | RecFunc (te,id,args,body) ->
          if te=t then
            match extr_arg_type te args with
              | Some (env2,t2) -> aux ((id,te)::env2@env) body t2
              | None -> false (* mismatch in number of arguments *)
          else false
      | Appln (e1,t1,args) ->
          begin
            match t1 with
              | Some t1a ->
                  begin
                    match extr_arg_type t1a args with
                      | Some (l2,t2) ->
                          if t=t2 then List.for_all (fun (ea,ta) -> aux env ea ta) l2
                          else false
                      | None -> false
                  end
              | None -> failwith "missing type : should call type_infer first"
          end
      | Let (ldecl,t0,body) ->
          match t0 with
          | Some te ->
            if te=t then
              let env2 = List.map (fun (t,v,b) -> (v,t)) ldecl in
              let nenv = env2@env in
                (aux nenv body te) && List.for_all (fun (t,_,b) -> aux nenv b t) ldecl
            else false
          | None -> failwith "missing type : should call type_infer first"

  in aux env e t





(* type inference, note that None is returned  *)
(*    if no suitable type is inferred *)
let rec type_infer_x (env:env_type) (e:sPL_expr) : sPL_type option * sPL_expr =
  match e with
    (* Infer the type only using the name and tags of the relation. 
       Then check whether the type inferred is equal to annotated tag.
       This checking is done is the type_check
       function above. *)
    | Relation ( ty , expr_lst) -> 
        begin
          (* First obtain relation name and relation tags*)
          let relation_name = 
            match ty with
              | RelationType ( nm , _ ) -> 
                 nm
              | _ -> failwith " Improperly defined relation: Type definition is incorrect. "
          and tags = 
            match ty with
              | RelationType ( _ , lst ) -> 
                 List.fold_right (fun (tg , _) b -> tg::b) lst []
              | _ -> failwith " Improperly defined relation: Type definition is incorrect. "
          (* Next, check if the tags repeat or not. This is as per our syntactic requirements. 
          We do so by using the sort_uniq function which sorts a list and removes duplcates. Clearly, if
          there are duplicate tags, the following equality will not hold true, in which case we fail to infer a
          type.*)
          in
          if not 
            (
              List.length 
              (
                List.sort_uniq
                (fun a b -> Pervasives.compare a b)
                tags
              ) = List.length tags
            )
          then (None , e)
          else 
            (* Infer type of first row. Check whether remaining rows have same type. *)
            match expr_lst with
                | [] -> (None , e) (* Relations cannot be empty *)
                | xh :: xt -> 
                  begin
                  (* First obtain a preliminary data type by looking at the head of the list*)
                   let init_type = 
                   List.fold_right
                   (
                    fun a b ->
                      match (type_infer_x env a) with
                        | (Some IntType, _) ->  (Some IntType) :: b
                        | (Some BoolType, _) -> (Some BoolType) :: b 
                        | _ -> None :: b  
                   )
                   xh
                   [] 
                   in
                   (* Next, check if this preliminary type is the same for the remaining rows*)
                   if (List.mem None init_type)
                   then (None , e) 
                   else 
                     let remaining_types_lst = 
                     (* Convert each row into its respective type list*)
                     List.map 
                      (
                        fun lst ->
                          List.fold_right
                           (
                            fun a b ->
                              match (type_infer_x env a) with
                                | (Some IntType , _) ->  (Some IntType) :: b
                                | (Some BoolType , _) -> (Some BoolType) :: b 
                                | _ -> None :: b  
                           )
                           lst
                           [] 
                      )
                      xt
                      in
                      (* Then check if for all the type lists are equal to the preliminary type list*)
                      if (List.for_all 
                      (fun el -> el = init_type)
                      remaining_types_lst)
                      (* If this is the case, then combine all the tags and inferred types for each column
                      into a pair list. Since the List.combine function throws errors when the lists are of unequal 
                      lengths (implying an incorrect type declaration), we use a try-with construct. *)
                      then  
                        try
                          let final_type =  
                          List.combine 
                          tags
                          ( List.map (fun (Some a) -> a) init_type ) (* This is the list of sPL types. *)
                          in
                          ( Some (RelationType (relation_name , final_type)), e)
                        with
                          | _ -> (None , e)
                      else
                        (None , e)
                  end 
         end
    (* Check whether the tags to be projected exist in the relation. 
    If they do, find the projected type. Note that the order of tags
    in the projected type follows the order of the original tags. *)
    | Projection (rel , tag_lst , _ ) -> 
        begin
          (* We ensure that the tag_lst is composed of ids at the syntactic (parser) level. 
             Next, we infer the type of the relation to be projected*)

          match (type_infer_x env rel) with
            |(Some ty , new_exp) -> 
               (* The expression to be projected may not even be a relation, 
               but may be a valid sPL expression. Hence we use the try-catch 
               statement. *)
               try 
                 let RelationType (relation_name , type_lst) = ty 
                 in 
                 (* Check whether all the tags appear at least once in the relation type*)
                 if 
                  (
                       List.for_all 
                       (
                         fun tag -> 
                           List.exists (fun (id , _) -> tag = id) type_lst
                       )
                       tag_lst
                  )
                 (* If this is the case, then find the projected type*) 
                 then  
                   let (projected_type_lst , _) = 
                   List.partition
                   (
                   fun (id , _ ) -> List.mem id tag_lst 
                   )
                   type_lst 
                   in 
                   let projected_type = RelationType (relation_name^"_p" , projected_type_lst) 
                   in
                   let new_expression = Projection (new_exp , tag_lst , Some projected_type)
                   in (Some projected_type , new_expression) 
                 else 
                   let new_expression = Projection (new_exp , tag_lst , None)
                   in 
                   (None , new_expression)
               with
                 |_ -> (None , e)
            |_ -> 
                let new_expression = Projection (new_exp , tag_lst , None)
                in 
                (None , new_expression)
        end  
    | Join (rel1 , rel2 , _) ->  
       begin
         match (type_infer_x env rel1) , (type_infer_x env rel2) with
            | (Some rel1_t , new_rel1 ) , (Some rel2_t , new_rel2 ) ->
               begin
                 try 
                   let RelationType (rel1_name , rel1_ty_lst) = rel1_t 
                   and RelationType (rel2_name , rel2_ty_lst) = rel2_t 
                   in 
                   let joined_lsts = (construct_join_type rel1_ty_lst rel2_ty_lst)
                   in 
                   let join_type = 
                    RelationType (rel1_name^"_j_"^rel2_name ,
                    joined_lsts)
                   in 
                   (* Type error if there are no common tags. *)
                   if (List.length joined_lsts = List.length rel1_ty_lst + List.length rel2_ty_lst)
                   then (None , e)
                   else
                      (* We use the modified expressions from the type inference. *)
                     let new_expression = Join (new_rel1 , new_rel2 , Some join_type) 
                     in (Some join_type , new_expression)
                 with
                   |_ -> (None , e)
               end
            | _ , _ -> 
               let new_expression = Join (rel1 , rel2 , None )
               in 
               (None , new_expression) 
       end
    | Selection1 (rel_exp , id1 , op , id2) -> 
       begin
    (* First ensure that the rel_exp has a correct type *)
        match (type_infer_x env rel_exp) with 
          | (Some rel_ty , new_rel_exp) -> 
             begin
               (* Next, check if id1 and id2 belong to the tag list. *)
               let RelationType (_ , tag_typ_lst) = rel_ty 
               in
               let tag_lst = 
               List.fold_right 
               (
                fun (tag , _) b -> 
                tag :: b
               ) 
               tag_typ_lst 
               []
               in
               if ( List.mem id1 tag_lst && List.mem id2 tag_lst )
               then 
               (* Finally check if a valid operator is used. *)
                 if List.mem op selection_op_id_lst 
                 then 
                   let final_exp = Selection1 (new_rel_exp , id1 , op , id2)
                   (* The selection will always have the same type as the original relation*) 
                   in ( Some rel_ty , final_exp ) 
                 else (None , e) 
               else (None , e)
             end
          | _ -> (None , e)
       end 
    | Selection2 (rel_exp , id1 , op , value) -> 
       begin
          match (type_infer_x env rel_exp) with 
          | (Some rel_ty , new_rel_exp) -> 
             begin
               (* Next, check if id1 belongs to the tag list. *)
               let RelationType (_ , tag_typ_lst) = rel_ty 
               in
               let tag_lst = 
               List.fold_right 
               (
                fun (tag , _) b -> 
                tag :: b
               ) 
               tag_typ_lst 
               []
               in
               if ( List.mem id1 tag_lst )
               then 
               (* Finally check if a valid operator is used and value is provided. *)
                 if 
                 (
                  List.mem op selection_op_id_lst 
                  &&
                  (
                    match (type_infer_x env value) with 
                      | (Some IntType  , _ ) | (Some BoolType , _ ) -> true
                      | _ -> false
                  )
                 )
                 then 
                   let final_exp = Selection2 (new_rel_exp , id1 , op , value)
                   (* The selection will always have the same type as the original relation*) 
                   in ( Some rel_ty , final_exp ) 
                 else (None , e) 
               else (None , e)
             end
          | _ -> (None , e)
       end
    | IntConst _ -> (Some IntType,e)
    | BoolConst _ -> (Some BoolType,e)
    | Var v -> let ty = get_type env v in (ty,e) 
    | UnaryPrimApp (op,arg) ->
        begin
          match op with
            | "~" ->
                let (at2,na2) = type_infer_x env arg in
                  (match at2 with
                    | Some IntType -> (at2, UnaryPrimApp (op,na2))
                    | _ -> (None,e))
            | "\\" ->
                let (at2,na2) = type_infer_x env arg in
                  (match at2 with
                    | Some BoolType -> (at2, UnaryPrimApp (op,na2))
                    | _ -> (None,e))
            | _ -> (None,e)
        end
    | BinaryPrimApp (op,arg1,arg2) ->
        begin
          match op with
            | "-" | "+" | "*" | "/"  ->
                let (at1,na1) = type_infer_x env arg1 in
                let (at2,na2) = type_infer_x env arg2 in
                  (match at1,at2 with
                    | Some IntType,Some IntType -> (at2, BinaryPrimApp (op,na1,na2))
                    | _ -> (None,e))
            | "<" | ">" | "=" ->
                let (at1,na1) = type_infer_x env arg1 in
                let (at2,na2) = type_infer_x env arg2 in
                  (match at1,at2 with
                    | Some IntType,Some IntType -> (Some BoolType, BinaryPrimApp (op,na1,na2))
                    | _ -> (None,e))
            | "&" | "|" ->
                let (at1,na1) = type_infer_x env arg1 in
                let (at2,na2) = type_infer_x env arg2 in
                  (match at1,at2 with
                    | Some BoolType,Some BoolType -> (Some BoolType, BinaryPrimApp (op,na1,na2))
                    | _ -> (None,e))
            | _ -> (None,e)
        end

    | Cond (e1,e2,e3) ->
        begin
          match type_infer_x env e1 with
            |(Some BoolType, cond) ->  (* The first expression must be of booltype *)
                let (at1,na1) = type_infer_x env e2 in
                let (at2,na2) = type_infer_x env e3 in
                  if at1 = at2 && at1!= None 
                  then (at1, Cond(cond, na1, na2)) (* that is, both e2 and e2 have the same VALID type (hence the check for None) *)
                  else (None, e)
            |_ -> (None, e)  
        end
    (* e1 must be bool type *)
    (* e2,e3 must be of the same inferred type *)

    | Func (te,args,body) ->
        begin

          match extr_arg_type te args with
            |Some (env1, ret_t)-> 
                begin
                  let ext_env = env1@env in
                    match (type_infer_x ext_env body) with
                      |(Some t , ex) ->
                          if (t = ret_t) then (Some te, Func(te, args, ex))
                          else (None, e)
                      |_ -> (None, e) 
                end

            |_ -> (None, e) 

        end


    (* te is the inferred function type *)
    (* infer the types of args and body *)
    (* args and body type must be consistent with te *)
    (* extend the env when checking type of body *)

    | RecFunc (te,id,args,body) -> 
        let env1 = (id, te)::env in

          begin

            match extr_arg_type te args with
              |Some (env2, ret_t)-> 
                  begin
                    let ext_env = env2@env1 in
                      match (type_infer_x ext_env body) with
                        |(Some t , ex) ->
                            if (t = ret_t) then (Some te, RecFunc(te, id, args, ex))
                            else (None, e)
                        |_ -> (None, e) 
                  end

              |_ -> (None, e) 

          end

    (* te is the inferred function type *)
    (* infer the types of args and body *)
    (* args and body type must be consistent with te*)
    (* extend the env when checking type of body *)

    | Appln (e1,_,args) ->
        begin 
          match (type_infer_x env e1) with
            |(Some t, e1') -> 
                begin
                  let func_type = t in
                    match (extr_arg_type func_type args) with
                      |Some (init_binding, ret_t) ->
                          begin
                            (* Check whether types of actual and formal parameters match. Return the list of identifiers. *)
                            let rec visit b acc = 
                              match b with
                                |(ex,t)::tail -> 
                                    begin
                                      (* Infer the type of an expression, and check whether the type matches the corresponding formal parameter type *)
                                      match (type_infer_x env ex) with
                                        |(Some ty,exp)->
                                            if (ty = t) then visit tail (exp::acc) else None
                                        |_ -> None
                                    end
                                |[] -> Some (List.rev (acc))
                            in 
                              match (visit init_binding []) with
                                |None -> (None,e) (* Implies that some type has not matched *)
                                |Some lst -> (Some ret_t, (Appln (e1',Some(ret_t) ,lst))) 
                          end
                      |_ -> Printf.printf("Hi") ; (None, e)
                end
            |(None, _) -> Printf.printf("Hi") ; (None,e) (* Implies that the function isn't well typed *)

          (* infer the type of e1 first *)
          (* infer the types of args *)
          (* check that args are consistent with inferred type *)
          (* remember to update _ with inferred type of e1 *)
        end
    | Let (ldecl,te,body) -> 
        (* the implementation for Let is given *)
        (* pick the type of local vars from ldecl *)
        let env2 = List.map (fun (t,v,b) -> (v,t)) ldecl in
        (* build an extended type environment for checking body *)
        let nenv = env2@env in
        (* infer the type of body *)
        let (nt1,nbody) = type_infer_x nenv body in
        (* infer the type of local definitions *)
        let ls_res = List.map (fun (t,v,b) -> (type_infer_x env b,v,t)) ldecl 
        in
          (* why did we use env rather than nenv when checking ldecl? *)
        match te with (* Annotated let body *)
          | Some t ->
             begin
               match nt1 with
                  | Some t1 -> 
                      (* check that body type is consistent *)
                      if t1=t
                      then 
                        (* check that local declarations are typed consistently *)
                        if List.for_all (fun ((t,e),_,t2) -> t=Some t2) ls_res 
                        then (nt1, Let(List.map (fun ((_,e),v,t)->(t,v,e)) ls_res, Some t1 ,nbody))
                        else (None,e)
                      else (None,e)
                  | None -> (None,e)
              end
          (* Unannotated let body *)
          | None -> 
              match nt1 with
                  | Some t1 -> 
                      (* Since no type annotation is present for body type 
                      we need not check if it is consistent *)
                      (*if t1=te then *)
                        (* check that local declarations are typed consistently *)
                      if List.for_all (fun ((t,e),_,t2) -> t=Some t2) ls_res 
                      then (nt1, Let(List.map (fun ((_,e),v,t)->(t,v,e)) ls_res, nt1 ,nbody))
                      else (None,e)  
                  | None -> (None,e)  
     

let rec type_infer (env:env_type) (e:sPL_expr) : sPL_type option * sPL_expr =
  Debug.no_1 "type_infer" pr_none pr_none (fun _ -> type_infer_x env e) e 

(* number of arguments for full application *)
(* Ex: num_of_arg (int->(int->int)->int) ==> 2 *)
let rec num_of_arg rt =
  match rt with
    | Arrow (_,t2) -> 1+(num_of_arg t2)
    | _ -> 0

(* determine if sufficient argument for type *)
(* if insufficient - return fresh id and residual type *)
(* get_partial int->int->int [2] ===> Some (["_tmp_1"],int->int *)
(* get_partial int->int->int [] ===> Some (["_tmp_1";"_tmp_2"],int->int->int *)
let get_partial (t:sPL_type) (args:'b list) =
  if not(!pa_removal_flag) then None
  else
    match extr_arg_type t args with
      | None -> None
      | Some (ls,rt) -> 
          let narg = num_of_arg rt in
            if narg=0 then None
            else Some (rt,(names # fresh_strs "_pa_var" narg))


let rec build_type ls bt =
  match ls with
    | [] -> bt
    | (t,_,_)::ls -> Arrow(t,build_type ls bt)


(* 
preprocessing to remove 
(i) partial application 
(ii) let construct
S.sPL_expr --> C.sPL_expr
*)


let trans_exp (e:sPL_expr) : C.sPL_expr  =
  let rec aux e =
    match e with
      | Relation (rt , r_lol) -> 
         let r_lol_new = 
         List.map 
         (
          fun a ->
            List.map 
            (fun b -> aux b)
            a
         )
         r_lol 
         in 
         C.Relation (rt , r_lol_new)
      | Projection (rel , tg , ty) -> 
         let new_rel = aux rel 
         in
         C.Projection (new_rel , tg , ty)
      | Join (rel1 , rel2 , ty) ->
         let new_rel1 = aux rel1 
         and new_rel2 = aux rel2
         in
         C.Join (new_rel1 , new_rel2 , ty)
      | Selection1 (rel_exp , id1 , op , id2) -> 
         C.Selection1 ((aux rel_exp) , id1 , op, id2)
      | Selection2 (rel_exp , id1 , op, value) -> 
         C.Selection2 ((aux rel_exp) , id1 , op, (aux value)) 
      | BoolConst v -> C.BoolConst v
      | IntConst v -> C.IntConst v
      | Var v -> C.Var v
      | UnaryPrimApp (op,arg) ->
          let varg = aux arg in
            (C.UnaryPrimApp (op,varg))
      | BinaryPrimApp (op,arg1,arg2) ->
          let varg1 = aux arg1 in
          let varg2 = aux arg2 in
            (C.BinaryPrimApp (op,varg1,varg2))
      | Cond (e1,e2,e3) ->
          let v1 = aux e1 in
          let v2 = aux e2 in
          let v3 = aux e3 in
            C.Cond (v1,v2,v3)
      | Func (t,vs,body) ->
          let nbody = aux body in
            C.Func (t,vs,nbody)
      | RecFunc (f,t,vs,body) ->
          let nbody = aux body in
            C.RecFunc (f,t,vs,nbody)
      | Appln (f,t,args) ->
          begin
            match t with
              | Some t1 ->
                  begin
                    let args = List.map aux args in
                    let f = aux f in
                      match get_partial t1 args with
                        | None ->  C.Appln (f,t1,args)
                        (* get_partial int->int->int [] ===> Some (["_tmp_1";"_tmp_2"],int->int->int *)
                        | Some (t2,ns) -> C.Func(t2,ns,C.Appln(f,t1,args@(List.map (fun v -> C.Var v) ns)))
                  end
              | _ -> failwith ("missing type : not possible")
          end
      | Let (ls, Some return_type,body) -> 
          begin
            let rec visit lst acc_type acc_id acc_expr = 
              match lst with
                |[] -> (List.rev (acc_type) , List.rev (acc_id) , List.rev (acc_expr))
                |(t, v, e)::tail -> visit tail (t::acc_type) (v::acc_id) (e::acc_expr)  
            in let (type_lst, id_lst, expr_lst) = visit ls [] [] [] 
            in 
            let rec visit_again t_lst = 
              match t_lst with
                |[] -> failwith "No arguments present in function application : not possible"
                |[h] -> Arrow (h, return_type) (* We expect at least one binding *)
                |h::t-> Arrow (h, (visit_again t))
            in let ty = visit_again type_lst
            in let func = Func (ty , id_lst , body)
            (* translate the let construct into an Appln construct and send to aux. 
            The above Appln case takes care of the rest*)
            in aux (Appln (func, (Some return_type), expr_lst))
          end

(* transform Let into a function application *)
(* build a correct type for the function from *) 
(* the type of arguments (local vars) and body *)
  in aux e

(* calling sPL parser *)
(*let parse_file (filename:string) : (string * sPL_expr) =
  SPL_parser.parse_file filename *)

(* set up for command argument
   using Sys and Arg modules *)
(* let usage = "usage: " ^ Sys.argv.(0) ^ " <filename>" *)
(* let file = ref ""  *)


(* Extra Assignment for 10% Bonus *)
(*
Currently types are given at the following 
places (or features):
(i) body of let
(ii) local definitions of let
(iii) function definition
(iv) recursive function definition
The extra assignment requires you to make their
type declaration optional. I suggest you do them 
gradually, starting with (i), then (ii) etc.
You must do the following for each:
(a) change the corresponding type of each
feature to option type in sPL.ml 
(b) change parser to make the type declaration 
optional for those features
(c) change type_infer to infer types when not given
(d) core language in sPLc.ml must have fully inferred type.
*)
