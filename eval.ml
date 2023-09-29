open MicroCamlTypes
open Utils
open List

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)


(* let rec getValue env e = 
  match e with
  | ID id -> let x = Hashtbl.find env id in if x = default then raise (RunError (id ^ " not initialized")) else x
  | Int int -> int 
   | Add (a, b) ->  (getValue env a) + (getValue env b)
  | Greater (a, b) ->  if (getValue env a) > (getValue env b) then 1 else falseInt
  | Equal (a, b) ->  if (getValue env a) = (getValue env b) then 1 else falseInt
  | Less (a, b) ->  if (getValue env a) < (getValue env b) then 1 else falseInt
  | Mult (a, b) ->  (getValue env a) * (getValue env b)
  | Concat (a, b) ->  mypow (getValue env a)  (getValue env b)
  | LParen a -> getValue env a
  | _ -> raise (RunError "not expression")  *)
let rec length lst =
  match lst with 
    |[] -> 0
    |_::t -> 1 + length t
;;

let strip_ID var = 
  match var with
  | ID x -> x
  |_-> failwith "not ID type"
;;

let first_tup (a,b) = a;;
let second_tup (a,b) = b;;
let hd lst = 
        match lst with
        []-> failwith "List empty!"
        |h::t-> h
;;
let check_env_var_equals_var env var =
  let env_tuple = hd env in
  if first_tup env_tuple = var then
    true
  else
    false
;;
let check_env_val_equals_bool env =
  let env_tuple = hd env in
  let env_ref = second_tup env_tuple in
  let env_val = !env_ref in
  match env_val with 
  |Bool x -> true
  |_ -> false
 
;;
let get_env_val env =
  let env_tuple = hd env in
  let env_ref = second_tup env_tuple in
  let env_val = !env_ref in
  env_val
;;  

let reverse_bool bool = 
  match bool with
  |Bool false -> Bool true
  |Bool true -> Bool false
  |_-> failwith "not Bool"
;;
let is_bool_object bool =  
  match bool with
  |Bool x -> true
  |_ -> false

let is_int_object int = 
  match int with
  |Int x -> true
  |_ -> false

let is_str_object string = 
  match string with
  |String x -> true
  |_ -> false
;;
let get_Int int = 
  match int with
  |Int x -> x
  |_-> failwith "not Int"
;;

let get_Str string = 
  match string with
  |String x -> x
  |_-> failwith "not String"
;;

let get_Bool bool = 
  match bool with
  |Bool x -> x
  |_-> failwith "not Bool"
;;

let get_object_type obj = 
  match obj with
  |Int _ -> Int 0
  |Bool _ -> Bool true
  |String _ -> String ""
  |Closure _ -> Closure ([], "", ID "")
;; 

 


(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
let rec eval_expr env ast = 
  match ast with
  | Value value -> value
  | ID var->(* if length env > 0 then
              if (check_env_var_equals_var env var) = true then 
                get_env_val env  
              else 
                  raise (DeclareError "Unbound variable")
            (* must be unbound if env length is 0 *)      
            else
              raise (DeclareError "Unbound variable") *)
              lookup env var
  | Not expr-> if length env > 0 then
                    let nots_val = eval_expr env expr in
                 
                    if (check_env_val_equals_bool env) = true then
                      reverse_bool nots_val
                    (* envs var was not a bool, type error *)
                    else
                      raise (TypeError "Type error, expected a bool")
                  (* envs var was different than ast var *)    
                    
                  
                  else
                    let nots_val = eval_expr env expr in
                    reverse_bool nots_val
  | Binop (op, expr1, expr2)->
                if op = Add then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    Int((get_Int int_object_1) + (get_Int int_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")


                else if op = Sub then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    Int((get_Int int_object_1) - (get_Int int_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")

                else if op = Mult then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    Int((get_Int int_object_1) * (get_Int int_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")

                else if op = Div then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    (* if they are both Ints, make sure the second isnt 0 before dividing *)
                    if ((get_Int int_object_2) = 0) then 
                      raise (DivByZeroError)
                    else
                      Int ((get_Int int_object_1) / (get_Int int_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")
                else if op = Greater then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    if ((get_Int int_object_1) > (get_Int int_object_2)) then
                      Bool true
                    else
                      Bool false
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")


                else if op = Less then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    if ((get_Int int_object_1) < (get_Int int_object_2))then
                      Bool true
                    else
                      Bool false
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")

                else if op = GreaterEqual then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    (* if its either greater than (1) or equal (0) return true *)
                    if ((get_Int int_object_1) >= (get_Int int_object_2)) then
                      Bool true
                    else
                      Bool false
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")

                else if op = LessEqual then
                  let int_object_1 = eval_expr env expr1 in
                  let int_object_2 = eval_expr env expr2 in
                  if ((is_int_object int_object_1) && (is_int_object int_object_2) = true) then
                    (* if its either less than (-1) or equal (0) return true *)
                    if ((get_Int int_object_1) <= (get_Int int_object_2)) then
                      Bool true
                    else
                      Bool false
                  else
                    raise (TypeError "Type error, expected both arguments to be Int")

                else if op = Concat then
                  let str_object_1 = eval_expr env expr1 in
                  let str_object_2 = eval_expr env expr2 in
                  if ((is_str_object str_object_1) && (is_str_object str_object_2) = true) then
                    String((get_Str str_object_1) ^ (get_Str str_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be String")
                

                else if op = Equal then 
                  let object_1 = eval_expr env expr1 in
                  let object_2 = eval_expr env expr2 in
                  if ((get_object_type object_1) = (get_object_type object_2)) then
                    if (get_object_type object_1 = Int 0) then
                      if ((get_Int object_1) = (get_Int object_2)) then
                        Bool true
                      else
                        Bool false
                    else if (get_object_type object_1 = String "") then
                      if ((get_Str object_1) = (get_Str object_2)) then
                        Bool true
                      else
                        Bool false
                    else if (get_object_type object_1 = Bool true) then
                      if ((get_Bool object_1) = (get_Bool object_2)) then
                        Bool true
                      else 
                        Bool false
                    (* we cannot compare two closures for equality *)    
                    else if ((get_object_type object_1 = Closure ([], "", ID "")) && (get_object_type object_2 = Closure ([], "", ID ""))) then
                      raise (TypeError "We cannot compare to closures for equality")
                    else
                      raise (TypeError "Something unexpected happened")
                  else
                    raise (TypeError "Type error, expected both arguments to be of same type")
                  
                else if op = NotEqual then 
                  let object_1 = eval_expr env expr1 in
                  let object_2 = eval_expr env expr2 in
                  if ((get_object_type object_1) = (get_object_type object_2)) then
                    if (get_object_type object_1 = Int 0) then
                      if ((get_Int object_1) <> (get_Int object_2)) then
                        Bool true
                      else
                        Bool false
                    else if (get_object_type object_1 = String "") then
                      if ((get_Str object_1) <> (get_Str object_2)) then
                        Bool true
                      else
                        Bool false
                    else if (get_object_type object_1 = Bool true) then
                      if ((get_Bool object_1) <> (get_Bool object_2)) then
                        Bool true
                      else 
                        Bool false
                    else if ((get_object_type object_1 = Closure ([], "", ID "")) && (get_object_type object_2 = Closure ([], "", ID ""))) then
                      raise (TypeError "We cannot compare to closures for equality")
                    else
                      raise (TypeError "Something unexpected happened")
                  else
                    raise (TypeError "Type error, expected both arguments to be of same type")


                else if op = Or then 
                  let bool_object_1 = eval_expr env expr1 in
                  let bool_object_2 = eval_expr env expr2 in
                  if ((is_bool_object bool_object_1) && (is_bool_object bool_object_2) = true) then
                    Bool((get_Bool bool_object_1) || (get_Bool bool_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Bool")
                
                else if op = And then 
                  let bool_object_1 = eval_expr env expr1 in
                  let bool_object_2 = eval_expr env expr2 in
                  if ((is_bool_object bool_object_1) && (is_bool_object bool_object_2) = true) then
                    Bool((get_Bool bool_object_1) && (get_Bool bool_object_2))
                  else
                    raise (TypeError "Type error, expected both arguments to be Bool")

                else
                  raise (TypeError "Something unexpected happened. Binop was followed by something unexpected.")
  | If (expr1, expr2, expr3)->
              let bool_object_1 = eval_expr env expr1 in
              if (is_bool_object bool_object_1) then
                if (bool_object_1 = Bool true) then
                  eval_expr env expr2
                else
                  eval_expr env expr3
              else
                raise (TypeError "Type error, expected first expression to be a Bool")
  (* | Let (id_name, is_rec, init_expr, body_expr)->
            
              (* if non recursive do this *)
              if (is_rec = true) then
                let v = eval_expr env init_expr in
                eval_expr (extend env id_name v) body_expr
              (* if recursive do this *)
              else
                let tempEnv = extend_tmp env id_name in update tempEnv id_name (eval_expr tempEnv init_expr) in eval_expr tempEnv body_expr
                (* let tmp = (extend_tmp env id_name) in
                let a = eval_expr tmp init_expr in
                update tmp id_name a  in
                eval_expr tmp body_expr *) *)
  | Let (id_name, is_rec, init_expr, body_expr) -> 
                                            (match is_rec with
                                            | false -> eval_expr (extend env id_name (eval_expr env init_expr)) body_expr
                                            | true -> let tmp = (extend_tmp env id_name) in
                                            let v = eval_expr tmp init_expr in
                                            update tmp id_name v;
                                            eval_expr tmp body_expr)
  | Fun (param_expr, body_expr) -> 
                                  Closure(env, param_expr, body_expr)
  | FunctionCall (closure_var, val_var) -> 
                                (match eval_expr env closure_var with
                                | Closure(environmentA, param_expr, body_expr) -> let tmp = extend environmentA param_expr (eval_expr env val_var) in eval_expr tmp body_expr
                                | _ -> raise (TypeError ("Not a function")))

                  
               

 (* 
  | Fun of (var, expr) -> 
  | If of expr * expr * expr = 
  | FunctionCall of expr * expr 
  | Let of var * bool * expr * expr *)
 (*  | failwith "something unexpected happened" *)


(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
   let eval_mutop env m = 
    match m with
    | NoOp -> (env, None)
    | Def (var, expr_var) -> let tmp = extend_tmp env var in let v = (eval_expr tmp expr_var) in update tmp var v; (tmp, Some v)
    | Expr (id_name) -> env, Some (eval_expr env id_name)
