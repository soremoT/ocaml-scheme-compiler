#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
exception X_should_not_happen;;                      
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

type rw =
  | W of var * (int list)
  | R of var * (int list);;

let rec lex_add_rec scope params exp =let shortcut  = (lex_add_rec scope params ) in 
  match exp with
        | Const(a) -> Const'(a)
        | Var(name) -> input_vars scope params exp name
        | If(if1,if2,if3) -> If'(shortcut if1,shortcut if2,shortcut if3)
        | Seq(lst) -> Seq'(List.map shortcut lst)
        | Set(a,b) -> Set' (shortcut a, shortcut b)
        | Def(a,b) ->Def'(shortcut a, shortcut b)
        | Or(lst) -> Or'(List.map shortcut lst)
        | LambdaSimple(plam,blam) -> LambdaSimple'(plam,lex_add_rec (params::scope) plam blam)
        | LambdaOpt(plam,vs,blam) -> LambdaOpt'(plam,vs,lex_add_rec ((params@[vs])::scope) (plam@[vs]) blam)(*order of params and scope matters for the search in Vars*)
        | Applic(op,lst)-> Applic'(shortcut op , List.map shortcut lst)

  and input_vars scope params exp name = if List.mem name params 
                                         then Var'(VarParam (name,get_location params name 0))
                                         else get_var2 scope name 0

  and get_var2 scope name major= match scope with
                          | [] -> Var'(VarFree(name))
                          | a::b -> if List.mem name a then Var'(VarBound(name,major,get_location a name 0)) else get_var2 b name (major+1)

  and get_location lst name place= match lst with 
                            | []-> raise X_syntax_error
                            | a :: b -> if a=name  then place else get_location b name (place+1)
  ;;

let rec tail_convert exp in_tp=match exp with
        | Const'(a) -> Const'(a)
        | Var'(a) -> Var'(a)
        | Box'(a) -> raise X_syntax_error
        | BoxGet'(a) -> raise X_syntax_error
        | BoxSet'(a,b) -> raise X_syntax_error
        | If'(a,b,c) -> If'(tail_convert a false , tail_convert b in_tp , tail_convert c in_tp)
        | Seq' (lst) ->Seq'(process_lst_of_tail lst in_tp)
        | Set'(a,b) ->Set'(tail_convert a in_tp, tail_convert b false )
        | Def'(a,b) ->Def'(tail_convert a false,tail_convert b in_tp)
        | Or'(lst) ->Or'(process_lst_of_tail lst in_tp)
        | LambdaSimple'(p,b) ->LambdaSimple'(p,tail_convert b true)
        | LambdaOpt'(p,vs,b) ->LambdaOpt'(p,vs,tail_convert b true)
        | Applic'(op,body) ->(match in_tp with
                            | true -> ApplicTP'(tail_convert op false , process_list body)
                            | false -> Applic'(tail_convert op false , process_list body))

        | ApplicTP'(op,body) -> raise X_syntax_error

  and process_list lst = List.map (fun x -> tail_convert x false) lst

  and process_lst_of_tail lst in_tp = match in_tp with
                                      | false ->List.map (fun x->tail_convert x false) lst
                                      | true ->if (List.tl lst) =[]
                                      then [tail_convert (List.hd lst) true] 
                                      else (tail_convert (List.hd lst) false)::process_lst_of_tail (List.tl lst) in_tp
        ;;

let rec rec_box exp = match exp with 
        | Const'(a) -> Const'(a)
        | Var'(a) -> Var'(a)
        | Box'(a) -> Box'(a)
        | BoxGet'(a) ->BoxGet'(a)
        | BoxSet'(a,b) -> BoxSet'(a, rec_box b)
        | If'(a,b,c) -> If'(rec_box a , rec_box b  , rec_box c )
        | Seq' (lst) ->Seq'(List.map rec_box lst )
        | Set'(a,b) ->Set'(rec_box a , rec_box b )
        | Def'(a,b) ->Def'(rec_box a ,rec_box b )
        | Or'(lst) ->Or'(List.map rec_box lst )
        | LambdaSimple'(p,b) ->LambdaSimple'(p,rec_box (box_simple p b))(*box this lambda params and call recusively to box next..*)
        | LambdaOpt'(p,vs,b) ->LambdaOpt'(p,vs,rec_box (box_simple (p@[vs]) b))(*..lambdas in the body with boxes on current params*)
        | Applic'(op,lst) -> Applic'(rec_box op ,List.map rec_box lst )
        | ApplicTP'(op,lst) -> ApplicTP'(rec_box op , List.map rec_box lst )
  

  and get_list_for_box params body = match params with
                                              | [] -> []
                                              | a::b ->if (decide_if_boxable (get_list_of_boxed a params [] body) ) then [a]@(get_list_for_box b body) else (get_list_for_box b body)

  and decide_if_boxable lst_of_vars =let read_lst = List.filter (fun x ->match x with | R(a,b) ->true | W(a,b)->false ) lst_of_vars in
                                    let write_lst =  List.filter (fun x ->match x with | R(a,b) ->false | W(a,b)->true ) lst_of_vars in
                                     let lst_bool =List.map (fun x ->for_each x read_lst) write_lst in
                                    if (write_lst=[]||read_lst=[]) then false else (List.mem (true) lst_bool)

  and for_each get lst1 = match lst1 with 
                      | [] -> false
                      | a::b -> (find_what_i_need get a) || (for_each get b)

  and find_out  lex1 lex2 s1 s2=
    if check_scope2 s1 s2
    then false 
    else true

    and check_scope2 s1 s2 = (List.mem true (List.map (fun x->List.mem x s1) s2))
   


  and find_what_i_need one_wr one_read = (match one_wr with
              | W(VarParam(name1,lex1),scope1) ->(match one_read with
                                    | R(VarParam(name2,lex2),scope2)->false
                                    | R(VarBound(name2,lex2,pp2),scope2) ->true
                                    | _ -> raise X_should_not_happen)

              | W(VarBound(name1,lex1,pp1),scope1) ->(match one_read with
                                    | R(VarParam(name2,lex2),scope2)->true
                                    | R(VarBound(name2,lex2,pp2),scope2) ->find_out lex1 lex2 scope1 scope2
                                    | _ -> raise X_should_not_happen)

              | _ -> raise X_should_not_happen)


  and box_simple params body =
      let list_of_params_to_box = get_list_for_box params body in
      let updated_b =update_body_rec list_of_params_to_box params body in
      let addition = get_list_of_sets list_of_params_to_box params in
      if addition = [] then body else make_new_body updated_b addition

  (*put the sets of params in front of the body*)
  and get_list_of_sets box_p params =match box_p with
        | [] ->[]
        | a::b ->   Set'(Var'(VarParam (a,get_location a params 0)),Box'(VarParam(a,get_location a params 0))) ::  (get_list_of_sets b params)
  (*just return index in list*)
  and get_location p1 lst index=match lst with
        | [] -> index
        | a::b ->if p1 = a then index else  get_location p1 b (index+1)
  and update_body_rec params_to_box original_params body =match params_to_box with
        | [] -> body
        | a :: b -> update_body_rec b original_params (update_body a original_params body)

  and make_new_body new_body addition = Seq'(addition@[new_body])(*used during addition of SetBox*)
and get_lst_scope s lst = match lst with 
              | []->[]
              | a::b->a@ (get_lst_scope s b)

and get_list_of_boxed param_to_box original_params scope body = let short = get_list_of_boxed param_to_box original_params  in
match body with 
    | Var'(VarParam(a,b)) ->
        if a=param_to_box 
        then [R(VarParam(a,b),scope)]
        else []

    | Var'(VarBound(a,b,c)) ->
        if a=param_to_box 
        then [R(VarBound(a,b,c),scope)]
        else []
    | BoxSet'(a,b) -> (short scope b)
    | If'(a,b,c) -> (short scope a)@ (short scope b )@ (short scope c )
    | Seq' (lst) ->(get_lst_scope scope (List.map (fun x ->short (scope) x ) lst ))
    | Set'(Var'(VarParam(a,b)),exp) -> 
        if a=param_to_box 
        then [W(VarParam(a,b),scope)]@( short scope exp )
        else short scope exp

    | Set'(Var'(VarBound(a,b,c)),exp) ->
        if a=param_to_box 
        then [W(VarBound(a,b,c),scope)]@( short scope exp )
        else short scope exp

    | Set'(a,b) ->(short scope a )@( short scope b )
    | Def'(a,b) ->(short scope a )@( short scope b )
    | Or'(lst) -> (List.fold_left (fun x y -> List.append x y) [] (List.map (fun x ->short (scope) x ) lst ) )

    | LambdaSimple'(p,b) ->
        if List.mem param_to_box p
        then []
        else short (scope@[(Random.int 1000)]) b

    | LambdaOpt'(p,vs,b) ->
        if (List.mem param_to_box p) || (param_to_box=vs)
        then []
        else short (scope@[(Random.int 1000)]) b
    | Applic'(op,lst) ->(short scope op)@(List.fold_left (fun x y -> List.append x y) [] (List.map (fun x ->short (scope) x ) lst ))
    | ApplicTP'(op,lst) -> (short scope op)@(List.fold_left (fun x y -> List.append x y) [] (List.map (fun x ->short (scope) x ) lst ))
    | _ -> []

  and update_body param_to_box original_params body  = let short = update_body param_to_box original_params in
    match body with 
        | Const'(a) -> Const'(a)

        | Var'(VarParam(a,b)) ->
            if a=param_to_box 
            then BoxGet'(VarParam(a,b))
            else Var'(VarParam(a,b))

        | Var'(VarBound(a,b,c)) ->
            if a=param_to_box 
            then BoxGet'(VarBound(a,b,c))
            else Var'(VarBound(a,b,c))
        | Var'(a) -> Var'(a)
        | Box'(a) -> Box'(a)
        | BoxGet'(a) ->BoxGet'(a)
        | BoxSet'(a,b) -> BoxSet'(a,short b)
        | If'(a,b,c) -> If'(short a , short b  , short c )
        | Seq' (lst) ->Seq'(List.map short lst )

        | Set'(Var'(VarParam(a,b)),exp) -> 
            if a=param_to_box 
            then BoxSet'(VarParam(a,b),short exp)
            else Set'(Var'(VarParam(a,b)),short exp) 

        | Set'(Var'(VarBound(a,b,c)),exp) ->
            if a=param_to_box 
            then BoxSet'(VarBound(a,b,c),short exp)
            else Set'(Var'(VarBound(a,b,c)),short exp) 

        | Set'(a,b) ->Set'(short a , short b )
        | Def'(a,b) ->Def'(short a ,short b )
        | Or'(lst) ->Or'(List.map short lst )

        | LambdaSimple'(p,b) ->
            if List.mem param_to_box p
            then LambdaSimple'(p,b)
            else LambdaSimple'(p,short b)

        | LambdaOpt'(p,vs,b) ->
            if (List.mem param_to_box p) || (param_to_box=vs)
            then LambdaOpt'(p,vs,b)
            else LambdaOpt'(p,vs,short b)

        | Applic'(op,lst) -> Applic'(short op ,List.map short lst )
        | ApplicTP'(op,lst) -> ApplicTP'(short op , List.map short lst )
        
;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = lex_add_rec [] [] e;;

let annotate_tail_calls e = tail_convert e false;;

let box_set e =rec_box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
(**
open Semantics;;
#trace run_semantics;;
#trace get_list_of_boxed;;

let a = LambdaSimple (["x"], Set (Var "x", Applic (LambdaSimple ([], Var "x"), [])));;

run_semantics a;;*)