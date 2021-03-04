#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  




 (*return true if name in list*)
let is_it_reserved name = List.mem name reserved_word_list;;

let rec is_args_legal args = match args with 
                            | [] -> true
                            | head::tail -> not (List.mem head tail)&& not (is_it_reserved head) && is_args_legal tail;;
let rec get_let_params ribs =match ribs with
                        | Pair(Pair(param,Pair(value,Nil)),next) ->param :: get_let_params next
                        | Nil -> []
                        | _ -> raise X_syntax_error ;;
let rec get_let_values ribs =match ribs with
                        | Pair(Pair(param,Pair(value,Nil)),next) ->value :: get_let_values next
                        | Nil -> []
                        | _ -> raise X_syntax_error ;;
let rec parse sexpr =(match sexpr with 
  | Bool(s) ->     Const(Sexpr (Bool(s)))
  | Number(s) ->   Const(Sexpr (Number(s)))  
  | Char(s) ->     Const(Sexpr (Char(s)))
  | String(s) ->   Const(Sexpr (String(s)))
  | TagRef(s) ->   Const(Sexpr (TagRef(s)))
  
  | Symbol(name) ->  get_symbol name
  | TaggedSexpr(head,Pair(Symbol("quote"),Pair(s,Nil))) ->Const(Sexpr (TaggedSexpr(head,s)))
  | TaggedSexpr(head,tail) ->Const(Sexpr (sexpr))(*maybe needs an update*)
  | Pair(Symbol("quote"),Pair(s,Nil)) ->Const(Sexpr (s))

  | Pair(Symbol("if"),Pair(first_exp,Pair(second_exp,third_exp))) ->get_if_exp first_exp second_exp third_exp
  | Pair (Symbol("lambda"),Pair(Symbol(name),body)) -> LambdaOpt([],name,convert_body_to_seq body)
  | Pair (Symbol("lambda"),Pair(args,body)) -> if is_legal_pair_list args then make_lambda_simple args body else make_lambda_opt args body
  (*disjunction OR *)
  | Pair(Symbol("or"),Nil) -> Const(Sexpr( Bool(false)))
  | Pair(Symbol("or"),Pair(a,Nil)) -> parse a
  | Pair(Symbol("or"),args) -> Or (check_and_parse args)
  (*says define needs to be variable so only Symbol is valid?*)           
  | Pair(Symbol("define"),Pair(Symbol(name),Pair(sexp,Nil))) -> Def(get_symbol name,parse sexp)
  | Pair(Symbol("set!"),Pair(var,Pair(body,Nil))) -> Set (parse var,parse body)
  (*Explicit Seq*)
  | Pair(Symbol("begin"),Nil) ->Const (Void)
  | Pair(Symbol("begin"),Pair(a,Nil)) -> parse a
  | Pair(Symbol("begin"),args) -> Seq (check_and_parse args)(*maybe add syntax error for bigin*)

  (*Macro expansions*)
  | Pair(Symbol("quasiquote"),Pair(exp,Nil)) -> parse (get_qq exp)

  | Pair(Symbol("cond"),body) ->(match body with
                                | Nil -> Const(Void)
                                |_ -> parse (get_cond body))

  | Pair(Symbol("let"),Pair(ribs,body)) -> parse (get_let ribs body) 

  | Pair(Symbol("and"),lst) -> parse (get_and_macro lst)
    (*define MIT*)
  | Pair(Symbol("define"),Pair(first,second)) ->parse (get_define_MIT first second)

  | Pair(Symbol("letrec"),Pair(params,ribs)) -> parse (get_letrec params ribs)
  | Pair (Symbol("let*"),Pair(params,ribs)) -> parse (get_let_star params ribs) 
  

  (*Applic :not sure if only legal list or improper as well, also can take any 2 pairs and make applic,should probably be last in match *)
  (*| Pair(a,Nil) ->parse a not sure if won't couse bug*)
  | Pair(app ,args) -> get_applic app args
  | _ ->    raise X_syntax_error 
)

  and get_applic app args = if is_legal_pair_list args 
                       then Applic(parse app,List.map parse (convert_pair_to_list args)) 
                       else raise X_syntax_error 
(*functions to return Exp value*)
  and get_letrec params ribs = let f = get_let_params params in
                               let exps = get_let_values params in
                               let f_exps =List.map2 (fun a b -> Pair(Symbol("set!"),Pair(a,Pair(b,Nil)))) f exps in
                               let args=(List.fold_right (fun first second -> Pair(first,second)) (f_whatever f) Nil )in
                               Pair(Symbol("let"),Pair(args,list_to_pair_2 f_exps ribs)) 
  
 and f_whatever f = List.map (fun a-> Pair (a,Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil))) f

  and list_to_pair_2 lst ribs = match ribs with
          | Nil ->List.fold_right (fun first second -> Pair(first,second) ) (lst@[Nil]) Nil
          | Pair(a,Nil)->List.fold_right (fun first second -> Pair(first,second) ) (lst@[a]) Nil
          |_ -> raise X_syntax_error

  and get_define_MIT first second =match first with
                                  | Pair(names,args )-> Pair(Symbol("define"),Pair(names,Pair(Pair(Symbol("lambda"),Pair(args,second)), Nil)))
                                  | _->  raise X_syntax_error 
                                  
  and get_and_macro lst =match lst with
                        | Nil -> Bool(true)
                        | Pair(a,Nil) ->a
                        | Pair(a,b) ->Pair (Symbol "if", Pair (a, Pair(Pair (Symbol "and", b),Pair (Bool false, Nil))))
                        | _->  raise X_syntax_error 

  and get_let_star params ribs=match params with
                              | Nil-> Pair(Symbol("let"),Pair(Nil,ribs))
                              | Pair(a,Nil)-> Pair(Symbol("let"),Pair(Pair(a,Nil),ribs))
                              | Pair(a,b)-> (Pair(Symbol("let"),Pair(Pair(a,Nil),get_let_star_ribs b ribs)))
                              | _ -> raise X_syntax_error 

  and get_let_star_ribs params ribs=Pair(Pair(Symbol("let*"),Pair(params,ribs)),Nil)
                                    

  and get_let ribs body = Pair(Pair(Symbol("lambda"),Pair(convert_list_to_pair(get_let_params ribs), body)),convert_list_to_pair (get_let_values ribs))

  and get_cond exp =match exp with
                  | Pair(Pair(Symbol("else"),expr),ribs) -> Pair(Symbol("begin"),expr)(*maybe need to check ribs?*)
                  | Pair(Pair(test,Pair(Symbol("=>"),Pair(expr,Nil))),ribs) ->cond_get_arrow_rib test expr ribs
                  | Pair(Pair(test,exp),ribs) ->if ribs = Nil
                                                then Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),exp),Nil)))
                                                else Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),exp),Pair(Pair(Symbol("cond"),ribs),Nil))))
                  | _ -> raise X_syntax_error 
  and cond_get_arrow_rib test expr ribs =let a =(if (ribs = Nil )then Nil else Pair
  (Pair (Symbol "rest",
    Pair
     (Pair (Symbol "lambda",
       Pair (Nil,
        Pair
         (Pair(Symbol("cond"),ribs),
         Nil))),
     Nil)),
  Nil) )in
  let b =(if (ribs = Nil) then Nil else Pair (Pair (Symbol "rest", Nil), Nil) )in
  Pair (Symbol "let",
  Pair
   (Pair (Pair (Symbol "value", Pair (test, Nil)),
     Pair
      (Pair (Symbol "f",
        Pair
         (Pair (Symbol "lambda",
           Pair (Nil, Pair (expr, Nil))),
         Nil)),
      a)),
   Pair
    (Pair (Symbol "if",
      Pair (Symbol "value",
       Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
        b))),
    Nil)))

  and get_qq exp = match exp with
        | Bool(s) ->     exp
        | Number(s) ->   exp
        | Char(s) ->     exp
        | String(s) ->   exp
        | TagRef(s) ->   exp
        | TaggedSexpr(_) -> (Pair(Symbol("quote"),Pair(exp,Nil)))(*probably not sure*)
        | Pair(Symbol("unquote"),Pair(body,Nil)) ->  body
        | Pair(Symbol("unquote-splicing"),x) -> raise X_syntax_error 
        | Nil -> (Pair(Symbol("quote"),Pair(Nil,Nil)))
        | Symbol(name) ->  (Pair(Symbol("quote"),Pair(Symbol(name),Nil)))
        | Pair (a,b) ->get_qq_match a b
        

  and get_qq_match a b =match a with 
                    | Pair(Symbol("unquote-splicing"),Pair(x,Nil))-> Pair(Symbol("append"),Pair(x,Pair(get_qq b,Nil)))
                    | _ -> match b with 
                                  | Pair(Symbol("unquote-splicing"),Pair(y,Nil)) ->Pair(Symbol("cons"),Pair(get_qq a,Pair(y,Nil)))
                                  | _ -> Pair(Symbol("cons"),Pair(get_qq a,Pair(get_qq b,Nil)))

                                  
  and get_symbol name =  if not(is_it_reserved name) then Var(name) else raise X_syntax_error 
  and check_and_parse args = if is_legal_pair_list args then List.map parse (convert_pair_to_list args) else raise X_syntax_error 

  and make_lambda_simple args body = if is_args_legal (convert_pair_to_string_list args) then LambdaSimple(convert_pair_to_string_list args,convert_body_to_seq body) else raise X_syntax_error 
  and convert_body_to_seq body =let lst = convert_pair_to_list body in 
                                          match lst with
                                          | [] ->raise X_syntax_error 
                                          | [x] -> parse x
                                          | _->  Seq (List.map parse (convert_pair_to_list body)) 
                                           
  and make_lambda_opt args body = let first_args = get_improper_list args in
                                  if (is_args_legal first_args) 
                                  then LambdaOpt(first_args,get_last_in_improper_list args,convert_body_to_seq body)
                                  else raise X_syntax_error 

(*functions to help parse Sexp*)

  and get_num_of_in_improper_list num pair =match pair with
                          | Pair(Symbol(curr),Symbol(last))-> num+1
                          | Pair(Symbol(curr),next) -> get_num_of_in_improper_list (num+1) next
                          | _->  raise X_syntax_error 

  and get_last_in_improper_list pair =match pair with
                          | Pair(Symbol(curr),Symbol(last))-> last
                          | Pair(Symbol(curr),next) -> get_last_in_improper_list next
                          | _->  raise X_syntax_error 

  and get_improper_list pair =match pair with
                          | Pair(Symbol(curr),Symbol(last))-> curr::[]
                          | Pair(Symbol(curr),next) -> curr::get_improper_list next
                          | _->  raise X_syntax_error 

  and get_if_exp a b c = match c with 
                          | Nil -> If(parse a , parse b,Const(Void))
                          | Pair (e,Nil) -> If(parse a , parse b ,parse e)
                          | _ -> raise X_syntax_error 


  and is_legal_pair_list l= match l with
                          |Pair(_,next)->is_legal_pair_list next
                          |Nil->true
                          |_->false

  and convert_pair_to_string_list pair = match pair with
                          | Pair(Symbol(curr),next) -> curr::convert_pair_to_string_list next
                          | Nil -> []
                          | _->  raise X_syntax_error 

  and convert_pair_to_list pair = match pair with
                          | Pair(curr,next) -> curr::convert_pair_to_list next
                          | Nil -> []
                          | _->  raise X_syntax_error 

  and convert_list_to_pair lst= List.fold_right (fun first second -> Pair(first,second)) lst Nil
  ;;
 

let tag_parse_expression sexpr = parse sexpr;;

let tag_parse_expressions sexpr =List.map tag_parse_expression sexpr;;


end;; (* struct Tag_Parser *)



