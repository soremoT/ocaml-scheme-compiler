#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

exception X_Sexpr_dont_exist;;
exception X_TaggedSexpr_Error;;
exception X_not_in_table;;
let rec rename_sexpr con i =  match con with 
                                | Nil -> Nil
                                | Bool(s) ->     Bool(s)
                                | Number(s) ->   Number(s) 
                                | Char(s) ->     Char(s)
                                | String(s) ->   String(s) 
                                | Symbol(name) ->  Symbol(name)
                                | Pair(a,b) ->Pair (rename_sexpr a i,rename_sexpr b i)
                                | TagRef(s) ->   TagRef(s^i)
                                | TaggedSexpr(a,b) ->  TaggedSexpr(a^i,rename_sexpr b i)
                             
                                

let rec rename2 con i = match con with
                  | Void -> Void
                  | Sexpr(a) -> Sexpr( rename_sexpr a i);;

let rec rename ast index= match ast with 
          | Const'(a) -> Const'(rename2 a index)
          | Var'(a) -> Var'(a)
          | Box'(a) -> Box'(a)
          | BoxGet'(a) -> BoxGet'(a)
          | BoxSet'(a,b) -> BoxSet'(a,rename b index)
          | If'(a,b,c) -> If'(rename a index, rename b index, rename c index)
          | Seq' (lst) ->Seq'(List.map (fun x -> rename x index) lst )
          | Set'(a,b) ->Set'(rename a index,rename b index)
          | Def'(a,b) ->Def'(rename a index,rename b index)
          | Or'(lst) ->Or'(List.map (fun x -> rename x index) lst )
          | LambdaSimple'(p,body) ->LambdaSimple'(p , rename body index )
          | LambdaOpt'(p,vs,body) ->LambdaOpt'(p ,vs ,rename body index)
          | Applic'(op,body) -> Applic'(rename op index ,List.map (fun x -> rename x index) body )
          | ApplicTP'(op,body) -> ApplicTP'(rename op index ,List.map (fun x -> rename x index) body );;
(*recieve asts and num to change tag names*)
let rec get_rename asts num =match asts with 
                | [] -> []
                | a :: b  -> rename a (string_of_int num) :: get_rename b (num+1);;
                (*first iteration to get const values*)
let rec get_const_tbl ast = match ast with
                  | Const'(a) -> [a]
                  | Var'(a) -> []
                  | Box'(a) -> []
                  | BoxGet'(a) -> []
                  | BoxSet'(a,b) -> get_const_tbl b 
                  | If'(a,b,c) -> get_const_tbl a @ get_const_tbl b @ get_const_tbl c 
                  | Seq' (lst) ->get_const_of_lst lst 
                  | Set'(a,b) ->get_const_tbl a @ get_const_tbl b
                  | Def'(a,b) ->get_const_tbl a @ get_const_tbl b
                  | Or'(lst) -> get_const_of_lst lst
                  | LambdaSimple'(p,body) ->get_const_tbl body
                  | LambdaOpt'(p,vs,body) ->get_const_tbl body
                  | Applic'(op,body) -> get_const_tbl op @ get_const_of_lst body
                  | ApplicTP'(op,body) -> get_const_tbl op @ get_const_of_lst body
                  
and get_const_of_lst lst =match lst with 
                    | [] -> []
                    | a::b ->  get_const_tbl a @ get_const_of_lst b
                  ;;
let is_eq_sexp a b=match a , b with 
              | Void , Void-> true
              | Sexpr(c) , Sexpr(d) ->sexpr_eq c d
              |_ -> false;;

let rec remove_duplicate lst new_lst=match lst with
                  | [] -> new_lst@[]
                  | a::b ->if List.exists (fun x-> is_eq_sexp a x) new_lst  then remove_duplicate b new_lst   else remove_duplicate b (new_lst@[a])
                  ;;
(*may be buggy if there are nested Tagged definitions-> no problem I think*)

let rec remove_taged exp = match exp with
                      | TaggedSexpr (a,b) -> remove_taged b
                      | Pair(a,b) ->Pair(remove_taged a ,remove_taged b)
                      | _ -> exp
                ;;
let rec get_tag_ref_lst lst=match lst with
                      | [] ->[]
                      | a :: b -> match a with 
                                | Void ->get_tag_ref_lst b
                                | Sexpr(c) ->get_ref c b

(*may be a problem but works for now*)
and get_ref c b =match c with
                                    | Bool(d) ->     get_tag_ref_lst b
                                    | Nil ->         get_tag_ref_lst b
                                    | Number(d)  ->  get_tag_ref_lst b
                                    | Char (d) ->    get_tag_ref_lst b
                                    | String (d) ->  get_tag_ref_lst b
                                    | Symbol(d) ->   get_tag_ref_lst b
                                    | Pair (d,e) ->  get_ref d b @ get_ref e b  @ get_tag_ref_lst b
                            | TaggedSexpr (d,e) ->    [(d,remove_taged e)]@  get_ref e b @get_tag_ref_lst b
                                    | TagRef (d) ->  get_tag_ref_lst b 
                      ;;
let rec expand lst =match lst with
                      | [] -> []
                      | a::b ->match a with
                              | Void ->[a] @ expand b
                              | Sexpr(c) ->get_expand c b

and get_expand c b =match c with
                | Bool(d) ->[Sexpr(c)] @expand b
                | Nil ->[Sexpr(c)] @expand b
                | Number(d)  ->[Sexpr(c)] @expand b
                | Char (d) ->[Sexpr(c)] @expand b
                | String (d) ->[Sexpr(c)] @expand b
                | Symbol(d) ->[Sexpr(String(d))]@[Sexpr(c)] @expand b
                | Pair (d,e) ->  get_expand d b @ get_expand e b @ [Sexpr(remove_taged c)] @ expand b
                | TaggedSexpr (d,e) ->get_expand e b @expand b
                | TagRef (d) ->[Sexpr(c)]@expand b 
                
;;

let rec convert_to_tbl lst offset table =match lst with
                        | [] -> table
                        | h :: t -> match h with
                              | Void ->                     convert_to_tbl t (offset+1) (table@[(h,(offset,get_void ))])
                              | Sexpr(Nil) ->               convert_to_tbl t (offset+1) (table@[(h,(offset,get_nil ))])
                              | Sexpr(Bool(a)) ->           convert_to_tbl t (offset+2) (table@[(h,(offset,get_bool a))])
                              | Sexpr(Number(Int(a))) ->    convert_to_tbl t (offset+9) (table@[(h,(offset,get_int a))])
                              | Sexpr(Number(Float(a))) ->  convert_to_tbl t (offset+9) (table@[(h,(offset,get_float a))])
                              | Sexpr(Char(a)) ->           convert_to_tbl t (offset+2) (table@[(h,(offset,get_char a))])
                              | Sexpr(String(a)) ->         convert_to_tbl t (offset+9+(String.length a)) (table@[(h,(offset,get_string a))])
                              | Sexpr(Symbol(a)) ->         convert_to_tbl t (offset+9) (table@[(h,(offset,get_symbol a table))])
                              | Sexpr(Pair(a,b)) ->         convert_to_tbl t (offset+17) (table@[(h,(offset,get_pair a b table))])
                              | Sexpr(TagRef(a)) ->         convert_to_tbl t (offset+9) (table@[(h,(offset,get_tagref a table))])
                              | Sexpr(TaggedSexpr(a,b)) -> raise X_TaggedSexpr_Error
                              
                              
and get_void   =  "MAKE_VOID"
and get_nil    =  "MAKE_NIL"
and get_bool a =  match a with
                    | true ->  "MAKE_BOOL("^(string_of_int 1)^")"
                    | false -> "MAKE_BOOL("^(string_of_int 0)^")"

and get_int a   = "MAKE_LIT_INT("^(string_of_int a)^")"
and get_float a = "MAKE_LIT_FLOAT("^(string_of_float a)^")"
and get_char a  = "MAKE_CHAR_LIT("^(convert_char a)^")"
and get_string a =let a=string_to_list a in
                  let a =(String.concat "," (List.map (fun x-> string_of_int(Char.code x)) a)) in
"MAKE_STRING_LIT "^a(*maybe needs a change *)
and get_symbol a t="MAKE_SYMBOL_LIT(const_tbl +"^(string_of_int (get_offset t (Sexpr(String(a)))))^")"
and get_pair a b t="MAKE_LITERAL_PAIR(const_tbl +"^(string_of_int (get_offset t (Sexpr(a))  )  )^", const_tbl +"^(string_of_int (get_offset t (Sexpr(b)  ))  )^")"
and get_tagref a t=""

and convert_char a =string_of_int(int_of_char a)

and get_intable1 (a,(b,c)) = a
and get_intable2 (a,(b,c)) = b
and get_intable3 (a,(b,c)) = c
and get_offset tbl sexpr =match tbl with 
                          | [] -> raise X_not_in_table
                          | a::b ->if is_eq_sexp sexpr (get_intable1 a) then get_intable2 a else get_offset b sexpr
                              ;;

let rec get_final_const cons_tbl reflst = match reflst with
                        | [] -> cons_tbl
                        | (name,ast)::b ->get_final_const (find_ref name cons_tbl ast cons_tbl) b

and find_ref  name cons_tbl ast originalcons_tbl= match cons_tbl with
                        | [] -> []
                        | (Sexpr(TagRef(name2)),(a,b))::tail ->if name=name2 
                        then [(Sexpr(TagRef(name2)),(a,"MAKE_TAGREF_LIT(const_tbl+"^(string_of_int (get_offset originalcons_tbl (Sexpr(ast))  )  )^")"))]@ find_ref name tail ast originalcons_tbl
                        else [(Sexpr(TagRef(name2)),(a,b))]@find_ref name tail ast originalcons_tbl
                        | head :: tail->[head]@find_ref name tail ast originalcons_tbl
;;
let flat_const asts = let lst1 = get_const_of_lst asts in
                      let flat1 = remove_duplicate lst1 [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))] in
                      let ref_lst = get_tag_ref_lst flat1 in
                      let expanded= expand flat1 in
                      let flat2 =remove_duplicate expanded [] in
                      let final_table =convert_to_tbl flat2 0 [] in
                        get_final_const  final_table ref_lst
                      
;;
let rec get_rename asts num =match asts with 
                | [] -> []
                | a :: b  -> rename a (string_of_int num) :: get_rename b (num+1);;
                (*first iteration to get const values*)
let rec make_fvars ast = match ast with
                  | Const'(a) -> []
                  | Var'(VarFree x) -> [x]
                  | Var'(a) -> []
                  | Box'(a) -> []
                  | BoxGet'(a) -> []
                  | BoxSet'(a,b) -> make_fvars b 
                  | If'(a,b,c) -> make_fvars a @ make_fvars b @ make_fvars c 
                  | Seq' (lst) ->get_free_of_lst lst 
                  | Set'(a,b) ->make_fvars a @ make_fvars b
                  | Def'(a,b) ->make_fvars a @ make_fvars b
                  | Or'(lst) -> get_free_of_lst lst
                  | LambdaSimple'(p,body) ->make_fvars body
                  | LambdaOpt'(p,vs,body) ->make_fvars body
                  | Applic'(op,body) -> make_fvars op @ get_free_of_lst body
                  | ApplicTP'(op,body) -> make_fvars op @ get_free_of_lst body
                  
and get_free_of_lst lst =match lst with 
                    | [] -> []
                    | a::b ->  make_fvars a @ get_free_of_lst b;;


let rec make_free_set lst new_lst =match lst with
                    | [] -> new_lst@[]
                    | a::b ->if List.exists (fun x->  a=x) new_lst  then make_free_set b new_lst   else make_free_set b (new_lst@[a])
                    ;;
let rec enumarate lst i = match lst with
                  | [] -> []
                  | a::b -> [(a,i)]@enumarate b (i+1);;

let primitives = 
             ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
              "null?", "is_null"; "char?", "is_char"; "string?", "is_string";
              "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
              "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
              "symbol->string", "symbol_to_string"; 
              "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
              "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
              "car","asm_car";"cdr","asm_cdr";"cons","asm_cons";
              "set-car!","asm_set_car";"set-cdr!","asm_set_cdr";"apply","asm_apply"
                  (* you can add yours here *)];;


let counter =ref 0;;
let next_value = fun()->counter:=(!counter) +1;
                                  !counter;;


let counter2 =ref 0;;
let next_value2 = fun()->counter2:=(!counter2) +1;
               !counter2;;
let remove_tag_def ast =match ast with 
                        | Void -> Void
                        | Sexpr(a)-> Sexpr(remove_taged a);;
                        (*FOR NOW MAGIC IS 555 NOT SURE IT NEEDS TO BE IN APPLIC *)
let rec get_generate consts fvars ast i j= match ast with 
                  | Const'(a) -> (match a with 
                                        | Sexpr(TagRef(_))-> ("\tSKIP_TYPE_TAG r12 ,const_tbl+"^(string_of_int (get_offset consts (remove_tag_def a)  ))^"\n"^"\tmov rax,r12\n")
                                        | _ ->("\tmov rax,const_tbl+"^(string_of_int (get_offset consts (remove_tag_def a)  ))^"\n")
                                        )

                  | Var'(a) ->generete_var consts fvars a
                  | Box'(a) -> "\tMALLOC rax , 8\n"
                              ^ "\tmov r12 , rax\n"
                              ^ (generete_var consts fvars a)
                              ^ "\tmov [r12] ,rax\n"
                              ^ "\tmov rax ,r12\n"

                  | BoxGet'(a) -> (generete_var consts fvars a) ^ "\tmov rax , qword [rax]\n"
                  | BoxSet'(a,b) ->  (get_generate consts fvars b i j) ^ "\tpush rax\n"
                                                                    ^ (generete_var consts fvars a) 
                                                                    ^ "\tpop qword [rax]\n"
                                                                    ^ "\tmov rax , SOB_VOID_ADDRESS\n"
                  | If'(a,b,c) ->let i=next_value2() in
                                    ";IFCHECK\n"^ (get_generate consts fvars a i j)
                                  ^"\tcmp rax , SOB_FALSE_ADDRESS\n"
                                  ^"\tje Lelse"^special i j^"\n"
                                  ^";IFTHEN\n"^(get_generate consts fvars b i j)
                                  ^"\tjmp Lexit"^special i j^"\n"
                                  ^"Lelse"^special i j ^":\n"
                                  ^";IFELSE\n"^(get_generate consts fvars c i j)
                                  ^"Lexit"^special i j^":\n"

                  | Seq' (lst) ->String.concat "\n"  (List.map (fun x -> (get_generate consts fvars x i j)^"\n") lst)

                  | Set'(Var'(VarFree(a)),exp) -> get_generate consts fvars exp i j
                                                  ^"\tmov qword [fvar_tbl+ "  ^(t_s (get_free_index fvars a ))  ^  "*8] , rax\n "
                                                  ^"\tmov rax , SOB_VOID_ADDRESS"
                  | Set'(Var'(VarParam(a,b)),exp) -> get_generate consts fvars exp i j
                                                    ^ "\tmov qword [rbp + 8 *(4 +" ^ t_s b ^ ")] , rax\n"
                                                    ^ "\tmov rax , SOB_VOID_ADDRESS\n"
                  | Set'(Var'(VarBound(a,major,minor)),exp) -> get_generate consts fvars exp i j
                                                              ^ "\tmov rbx , qword [rbp + 8 * 2]\n"
                                                              ^ "\tmov rbx , qword [rbx + 8 * " ^ t_s major ^"]\n"
                                                              ^ "\tmov qword [rbx + 8 * "  ^ t_s minor ^"] , rax\n" 
                                                              ^ "\tmov rax , SOB_VOID_ADDRESS\n" 
                  | Set'(a,b) ->raise X_Sexpr_dont_exist
                  | Def'(Var'(VarFree(name)),b) ->   get_generate consts fvars b i j
                                                  ^ "\tmov qword[fvar_tbl+"^(t_s (get_free_index fvars name))^"*8] , rax\n"
                                                  ^ "\tmov rax , SOB_VOID_ADDRESS\n"
                  | Def'(a,b) ->raise X_Sexpr_dont_exist
                  | Or'(lst) -> let i=next_value2() in
                                  (String.concat ("\tcmp rax ,SOB_FALSE_ADDRESS\n\tjne Lexit"^special i j^"\n" )
                                 (List.map (fun x -> (get_generate consts fvars x i j)  ) lst) ) ^ "Lexit" ^(special i j )^":\n"
                  | LambdaSimple'(p,body) ->generate_simple consts fvars p body i j
                  | LambdaOpt'(p,vs,body) ->generate_optional consts fvars p vs body i j
                  | Applic'(op,body) ->let i=next_value2() in
                                        "\tpush 555\n"^(String.concat "" (List.map (fun x->(get_generate consts fvars x i j)^"\tpush rax\n" ) (List.rev body)))
                                        ^"\tpush "^t_s (List.length body)^"\n"
                                        ^(get_generate consts fvars op (i+1) j)
                                        ^"\tcmp TYPE(rax) ,T_CLOSURE\n"
                                          ^"\tje ok"^special i j
                                          ^"\n\tcall problem\n"
                                          ^"ok"^special i j^":"
                                          ^"\n\tCLOSURE_ENV rdx , rax\n"
                                          ^"\tpush rdx\n"
                                          ^"\tCLOSURE_CODE rdx , rax\n"
                                          ^"\tcall rdx\n"
                                          ^return_env (special i j)

                  | ApplicTP'(op,body) ->let i=next_value2() in
                                       ";APPLICTP START\n"^"\tpush 555\n"^(String.concat "" (List.map (fun x->(get_generate consts fvars x i j)^"\tpush rax\n" ) (List.rev body)))
                                        ^"\tpush "^t_s (List.length body)^"\n"
                                        ^(get_generate consts fvars op (i+1) j)
                                        ^"\tcmp TYPE(rax) ,T_CLOSURE\n"
                                          ^"\tje ok"^special i j
                                          ^"\n\tcall problem\n"
                                          ^"ok"^special i j^":"
                                          ^"\n\tCLOSURE_ENV rdx , rax\n"
                                          ^"\tpush rdx\n"
                                          ^"\tpush qword [rbp+8*1] \n"
                                          ^"\tpush qword[rbp]\n"
                                          ^"\tSHIFT_FRAME "^t_s ((List.length body)+5)^"\n"
                                          ^"\tpop rbp\n"
                                          ^"\tCLOSURE_CODE rdx , rax\n"
                                          ^"\tjmp rdx\n"
                                  

and return_env str="\tadd rsp , 8*1\n"
                ^"\tpop rbx\n"
                ^"\tshl rbx , 3\n" 
                ^"\tadd rsp , rbx\n"
                ^"\tcmp qword[rsp],555\n"
                ^"\tjne applic_skip_magic"^str^"\n"
                ^"\tadd rsp , 8\n"
                ^"\tapplic_skip_magic"^str^":\n"

and special i j = (t_s i)^(t_s j)
and get_free_index fvars name =match fvars with
          | [] ->raise X_not_in_table
          | (x,y)::b -> if name=x then y else get_free_index b name 

and t_s s = string_of_int s           
and generete_var consts fvars a  =match a with 
                    | VarFree (str) -> "\tmov rax , qword [fvar_tbl+ "  ^(t_s (get_free_index fvars str ))  ^  "*8]\n"
                    | VarParam (str,minor) ->"\tmov rax , qword [rbp + 8 *(4 + "^(t_s minor)^")]\n"
                    | VarBound (str,major,minor) ->"\tmov rax , qword [rbp + 8 * 2]\n"^
                                                   "\tmov rax , qword [rax+ 8 * " ^ t_s major ^"]\n"^
                                                   "\tmov rax , qword [rax + 8 * "  ^ t_s minor ^"]\n"  

and generate_simple consts fvars p body i j = let i=next_value2() in
                                              let label =special i j in
                                              let env_size = t_s (j+1) in
                                              "\tMALLOC r12 , 8*"^env_size^"\n" 
                                              ^"\tmov r13 ,[rbp+2*8];lexical env\n"
                                             ^ "\tlea r14 ,[r12+8] ;offset1 memory\n"
                                             ^ "\tmov r15 , "^t_s j^";size of env\n"
                                             ^ "start_env"^label^":\n"
                                             ^ "\tcmp r15 ,0\n"
                                            ^  "\tje done_env"^label^"\n"
                                             ^ "\tmov rcx, qword[r13] \n"
                                             ^ "\tmov qword[r14] , rcx\n"
                                             ^ "\tadd r13 ,8;next env\n"
                                             ^ "\tadd r14 ,8;next new space\n"
                                             ^ "\tsub r15 ,1\n"
                                             ^" \tjmp start_env"^label^"\n"
                                             ^ "done_env"^label^":\n"
                                             ^"\tmov r8 ,[rbp+8*3];num of params\n"
                                             ^"\tshl r8 ,3\n"
                                              ^"\tMALLOC r9,r8\n"
                                              ^"\tshr r8 ,3\n"
                                              ^"\tpush r12;save env for closure\n"
                                              ^"\tmov [r12],r9 ;mov memory pointer to point to new memory\n"
                                             ^"\tlea r10 ,[rbp+8*4]\n"
                                             ^" start_param"^label^":\n"
                                              ^"\tcmp r8 ,0\n"
                                            ^"\tje end_param"^label^"\n"
                                            ^"\tsub r8 ,1 \n"
                                            ^"\tmov rbx, [r10]\n"
                                            ^"\tmov [r9], rbx\n"
                                            ^"\tadd r9 ,8\n"
                                            ^"\tadd r10 , 8\n"
                                            ^"\tjmp  start_param"^label^"\n"
                                            ^" end_param"^label^":\n"
                                            ^"\tpop rbx\n"
                                          
                                            ^"\tMAKE_CLOSURE(rax,rbx,Lcode"^label^")\n"
                                            ^"\tjmp Lcont"^label^"\n"
                                            ^"Lcode"^label^":\n"
                                            ^"\tpush rbp\n"
                                            ^"\tmov rbp ,rsp\n"
                                            ^get_generate consts fvars body i (j+1)
                                            ^"\tleave\n"
                                            ^"\tret\n"
                                            ^"Lcont"^label^":\n"



and generate_optional consts fvars p vs body i j = let i=next_value2() in
                                            let label =special i j in
                                                    let expected = t_s (List.length p) in
                                                   let env_size = t_s (j+1) in
                                              "\tMALLOC r12 , 8*"^env_size^"\n" 
                                              ^"\tmov r13 ,[rbp+2*8];lexical env\n"
                                             ^"\tlea r14 ,[r12+8] ;offset1 memory\n"
                                             ^"\tmov r15 , "^t_s j^";size of env\n"
                                             ^"start_env"^label^":\n"
                                             ^"\tcmp r15 ,0\n"
                                            ^"\tje done_env"^label^"\n"
                                             ^ "\tmov rcx, qword[r13] \n"
                                             ^ "\tmov qword[r14] , rcx\n"
                                             ^ "\tadd r13 ,8;next env\n"
                                             ^ "\tadd r14 ,8;next new space\n"
                                             ^ "\tsub r15 ,1\n"
                                             ^" \tjmp start_env"^label^"\n"
                                             ^ "done_env"^label^":\n"
                                             ^"\tmov r8 ,[rbp+8*3];num of params\n"
                                             ^"\tshl r8 ,3\n"
                                              ^"\tMALLOC r9,r8\n"
                                              ^"\tshr r8 ,3\n"
                                              ^"\tpush r12;save env for closure\n"
                                              ^"\tmov [r12],r9 ;mov memory pointer to point to new memory\n"
                                             ^"\tlea r10 ,[rbp+8*4]\n"
                                             ^"start_param"^label^":\n"
                                              ^"\tcmp r8 ,0\n"
                                            ^"\tje end_param"^label^"\n"
                                            ^"\tsub r8 ,1 \n"
                                            ^"\tmov rbx, [r10]\n"
                                            ^"\tmov [r9], rbx\n"
                                            ^"\tadd r9 ,8\n"
                                            ^"\tadd r10 , 8\n"
                                            ^"\tjmp  start_param"^label^"\n"
                                            ^" end_param"^label^":\n"
                                            ^"\tpop rbx\n"
                                            ^"\tMAKE_CLOSURE(rax,rbx,Lcode"^label^")\n"
                                            ^"\tjmp Lcont"^label^"\n"
                                            (*START of OPTIONAL*)
                                            ^"Lcode"^label^":\n"
                                            ^"\tpush rbp\n"
                                            ^"\tmov rbp ,rsp\n"
                                            ^"\tmov rbx ,"^expected^"\n"
                                            ^"\tmov rcx,PARAM_COUNT ;actual num of params\n"
                                            ^"\tcmp rcx ,rbx\n"
                                            ^"\tjge fine"^label^"\n"
                                            ^"\tcall problem ;recieved smaller than actual\n"
                                            ^"fine"^label^":\n"
                                            ^"\tcmp rbx , rcx \n"
                                            ^"\tje no_optional"^label^"\n"
                                            ^"\tlea rdx , [rbp + (3+rcx)*8] ;move address of optional to rdx\n"
                                            ^"\tpush rcx\n"
                                            ^"\tmov r15 ,rcx\n"
                                            ^"\tadd r15 ,3 ;the number to shift\n"
                                            ^"\tdec r15 ;dec for pair insert\n"
                                            ^"\tsub rcx,rbx\n"  
                                            ^"\tMAKE_OP_PAIR rax,rdx,rcx ;save in r12 rdx isstart of\n"
                                            ^"\tpop rcx;actual num of params\n"  
                                            ^"\tlea r14 ,[rbp + (3+rcx)*8]\n"
                                            ^"\tmov r13 ,rax;save pair\n"
                                            ^"\tmov [r14] ,r13 ;mov pair to last place rbp+holds the pair now\n"
                                            ^"\tdec rcx\n"
                                            ^"\tlea r13 ,[rbp + (3+rcx)*8];just before the pair lst\n"
                                            ^"\tlea r12 , [rbp+(3+rbx)*8]\n"
                                            ^"\tsub rcx ,rbx\n"
                                            ^"\tcmp rcx ,0\n"
                                            ^"\tje adjusted"^label^";if stack had 1 extra no need for adjust\n"
                                            ^"\tCOPY_FRAME r12 ,r13 ,r15\n"
                                            ^"\tshl rcx ,3\n"
                                            ^"\tadd rbp ,rcx ;addjust stack for distance\n"
                                            ^"\tmov rsp ,rbp\n"
                                            (*END of with args*)
                                            ^"\tjmp adjusted"^label^"\n"
                                            ^"no_optional"^label^":\n"
                                            ^"\tlea r14 , [rbp + (4+rcx)*8];address of magic\n"
                                            ^"\tmov r13 ,SOB_NIL_ADDRESS;save pair\n"
                                            ^"\tmov [r14] ,r13 ;mov pair to last place rbp+holds the pair now\n"
                                            ^"\tjmp adjusted"^label^"\n"
                                            ^"adjusted"^label^":\n"
                                            ^"\tmov rbx ,"^expected^";increase expected by 1 for the pair/lst\n"
                                            ^"\tadd rbx ,1\n"
                                            ^"\tmov [rbp+8*3] ,rbx\n"
                                            (*end of optional*)
                                            ^"\tmov rbp,rsp\n"
                                            ^get_generate consts fvars body i (j+1)
                                            ^"\tleave\n"
                                            ^"\tret\n"
                                            ^"Lcont"^label^":\n"
;;

                                              

let get_p lst= List.map (fun (x,y)->x ) lst ;;
module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = flat_const (get_rename asts 0);;
  let make_fvars_tbl asts = enumarate(make_free_set ((get_p primitives)@(List.fold_left (fun x y -> List.append x y) [] (List.map make_fvars asts) ) ) []) 0;;
  let generate consts fvars e = let ast = (rename e  (string_of_int (next_value()-1) )  )
                              in   get_generate consts fvars ast (next_value2()) 0
  ;;
end;;
(************************************test code***************************************************************)


(*
open Code_Gen;;


#trace generate;;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;
let infile = Sys.argv.(1);;
let ast = string_to_asts(file_to_string infile);;
let b =make_consts_tbl ast;;

let c =make_fvars_tbl ast;;

let d =  String.concat "\n"  (List.map (fun qq -> (generate b c qq) ^ "\n\tcall write_sob_if_not_void\n") ast) ;;



print_string d;;


let g =next_value();;
print_string(string_of_int g)

 


problem with tagged expr in lists create unnessesry objects
functions to recheck  expand and duplicate ,get_tag_ref_lst
*)