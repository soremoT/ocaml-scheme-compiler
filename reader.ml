
#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_not_in_char_list;;
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  


(*print_string  ( (Reader.read_sexpr "fuck"));;
print_string "hellla\n"
*)
(*convert radix letter to number*)

let get_radix_num sym=match sym with
                      | '0'-> 0
                      | '1'-> 1
                      | '2'-> 2
                      | '3'-> 3
                      | '4'-> 4
                      | '5'-> 5
                      | '6'-> 6
                      | '7'-> 7
                      | '8'-> 8
                      | '9'-> 9
                      | 'a'-> 10
                      | 'b'-> 11
                      | 'c'-> 12
                      | 'd'-> 13
                      | 'e'-> 14
                      | 'f'-> 15
                      | 'g'-> 16
                      | 'h'-> 17
                      | 'i'-> 18
                      | 'j'-> 19
                      | 'k'-> 20
                      | 'l'-> 21
                      | 'm'-> 22
                      | 'n'-> 23
                      | 'o'-> 24
                      | 'p'-> 25
                      | 'q'-> 26
                      | 'r'-> 27
                      | 's'-> 28
                      | 't'-> 29
                      | 'u'-> 30
                      | 'v'-> 31
                      | 'w'-> 32
                      | 'x'-> 33
                      | 'y'-> 34
                      | 'z'-> 35
                      | _ ->raise X_not_in_char_list;;
let rec get_float_point num =if num<1.0 then num else get_float_point (num/.(10.0));;
let convert_to_num num=int_of_string (list_to_string num);;
let get_some_float sym = (float_of_int (get_radix_num sym));;
let rec answer_for base len nums_as_list=
                                  match len with
                                        | 0 -> 0.0
                                        | _ -> ((float_of_int base) **(float_of_int (len-1))*. (get_some_float(List.hd nums_as_list)))+.(answer_for base (len-1) (List.tl nums_as_list) );;
let convert_radix_to_decimal  op_base nums_as_list =
  if (List.hd nums_as_list = '-') then -1.0 *. (answer_for (convert_to_num (op_base) ) ((List.length nums_as_list-1)) (List.tl nums_as_list))
  else (if(List.hd nums_as_list = '+') then (answer_for (convert_to_num ( op_base) ) ((List.length nums_as_list)-1) (List.tl nums_as_list)) 
  else (answer_for (convert_to_num op_base) (List.length nums_as_list) nums_as_list))
  ;;
let rec radix_f base floats exponent len =
                  match len = exponent with
                   | true -> (base ** exponent) *.(float_of_int(get_radix_num(List.hd floats)))
                   | false -> (base ** exponent) *.(float_of_int(get_radix_num(List.hd floats))) +.(radix_f base (List.tl floats) (exponent -.1.0 ) len)
;;       

let convert_radix_to_float op_base nums_as_list floats =let a =( -1.0*.(float_of_int(List.length floats))) in
                                                        let b = (radix_f (float_of_int (convert_to_num op_base)) floats  (-1.0 ) a) in
  if (List.hd nums_as_list = '-') then -1.0 *. (  (answer_for (convert_to_num (op_base) ) ((List.length nums_as_list-1)) (List.tl nums_as_list)) +.b  )
  else (if(List.hd nums_as_list = '+') then( (answer_for (convert_to_num ( op_base) ) ((List.length nums_as_list)-1) (List.tl nums_as_list)) +. b)
  else ( (answer_for (convert_to_num op_base) (List.length nums_as_list) nums_as_list)  +. b )  )
  ;;
open PC;;
let radix_nums = disj_list [range '0' '9';pack (range_ci 'A' 'Z') (fun x->lowercase_ascii x);one_of "+-"];;


let get1 (a,_) = a;;
(*function from recitation lessons*)
let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
    nt;;


(*comment related parsers*)
let nt_start_comment = pack (char ';') (fun x -> [x]);;
let nt_new_line =pack (char '\n')(fun x->[x]);;
let nt_comment_end = disj nt_end_of_input nt_new_line;;
let nt_parse_untill nt1 nt2= star (diff nt1 nt2);;



(*parse to check whether exp is ended legaly only accept single char parsers*)
let not_end nt= (disj (pack nt (fun x->[x])) nt_end_of_input );;(*might need to add additional char parser stop conditions like ";"*)
let pack_char nt =(pack nt (fun x->Nil));;
let reuse_dot_char=(pack_char(char '.') );;
let reuse_plus_char=(pack_char(char '+') );;
let reuse_minus_char=(pack_char(char '-') );;
let symbol_char = disj_list [range '0' '9';pack (range_ci 'A' 'Z') (fun x->lowercase_ascii x);one_of "!$^*-_=+<>?/:"];;
let nt_sym= disj_list [range '0' '9';pack (range_ci 'A' 'Z') (fun x->lowercase_ascii x);one_of ".!$^*-_=+<>?/:"];;
let pack_str str num = pack (word_ci str)(fun x-> (char_of_int num));;
let left_paren =pack_char (char '(');;
let right_paren =pack_char (char ')');;
let char_prefix = word "#\\";;


let convert_to_float num = float_of_string (list_to_string num);;
let get_float_obj a b =(convert_to_float a)+.((get_float_point(convert_to_float b) ));;
let get_sexp_match x = match x with 
                    | Symbol(x)-> x
                    | TagRef(x)-> x
                    | _ -> "mistake";;
let get_symbol_exp x =match x with 
                    | Symbol(x)-> x
                    | _ -> "mistake";;
let rec check_tag_reference_in_sexp sexp name = match sexp with 
                                              | Bool(exp)-> true
                                              | Nil-> true
                                              | Number(exp)-> true
                                              | Char(exp)-> true
                                              | String(exp)-> true
                                              | Symbol(exp)-> true
                                              | Pair(a,b)-> (check_tag_reference_in_sexp a name) && (check_tag_reference_in_sexp b name)
                                              | TaggedSexpr(a,b)->if a=name then false else (check_tag_reference_in_sexp b name)
                                              | TagRef(a)-> true;;

let rec nt_sexpr str_list = 

 disj_list  [nt_radix;getBool;nt_sce_not;getNumber;nt_symbol;nt_string;nt_char;nt_quotes;nt_nil;nt_lists;get_tag_exp]str_list

and get_tag_exp str =( disj nt_tagged_expr nt_tag_ref )str
and getBool str = disj_list[nt_bool_f;nt_bool_t]str
and getNumber str =disj_list [usigned_integer;signed_integer1;signed_integer2;uns_float;signed_float1;signed_float2]str

  (*parsers for skiping comments*)
and line_comment str = pack (caten nt_start_comment (nt_parse_untill nt_any nt_comment_end )) (fun (_) -> Nil) str
and skip_all str_list  = star(disj_list[pack_char nt_whitespace;line_comment;sexpr_comment] )str_list
and sexpr_comment str_list = (pack(caten (word "#;")(skip nt_sexpr))((fun (_) -> Nil)))str_list
and skip nt = make_paired skip_all skip_all nt 

and nt_bool_f str =(pack(word_ci "#f") (fun n->Bool(false)))str
and nt_bool_t str=(pack (word_ci "#t")(fun n->Bool(true)))str
and nt_symbol str = (pack ( plus symbol_char ) (fun x->Symbol(list_to_string x)))str
and is_it_a_symbol nt =(not_followed_by nt nt_sym)

and signed_integer1 str = is_it_a_symbol ( pack  (caten (pack_char(char '+') ) nt_digit ) (fun (_,x)-> Number(Int(convert_to_num x))))str
and signed_integer2 str = is_it_a_symbol( pack (caten (pack_char(char '-') ) nt_digit ) (fun (_,x)-> Number(Int(-1*convert_to_num x))))str
and usigned_integer str =is_it_a_symbol (pack  nt_digit (fun a-> Number(Int(convert_to_num a))))str
and uns_float str =is_it_a_symbol(pack (caten(caten nt_digit (pack_char (char '.'))) nt_digit ) (fun (((a,c),b))-> Number(Float(   get_float_obj a b  ) )))str
and signed_float1 str =is_it_a_symbol(pack (caten(caten (caten reuse_plus_char nt_digit) reuse_dot_char) nt_digit ) (fun ((((a,b),c),d))-> Number(Float(get_float_obj b d))) )str
and signed_float2 str =is_it_a_symbol(pack (caten(caten(caten  reuse_minus_char  nt_digit )reuse_dot_char) nt_digit) (fun ((((a,b),c),d))-> Number(Float(-1.0*.(get_float_obj b d)))) )str



and string_literal_char str = (guard nt_any (fun x-> if (x = '\"') then false else( if  (x = '\\') then false else true) )) str
and string_meta_char str = disj_list [pack_str "\\r" 13 ; pack_str "\\n" 10 ; pack_str "\\t" 9 ; pack_str "\\f" 12 ; pack_str "\\\\" 92 ; pack_str "\\\"" 34]str
and string_char str =( star(disj string_literal_char string_meta_char) )str
and nt_string str =(pack (caten(caten (pack_char (char '\"'))  string_char) (pack_char (char '\"')) ) (fun ((_,a),_) -> String(list_to_string a)))str 

(*most of the parsers just check last letter to be  space or endofinput otherwise cases are sensitive*)
and named_char str = disj_list[pack_str "nul" 0 ; pack_str "newline" 10 ; pack_str "return" 13  ; pack_str "tab" 9  ; pack_str "page" 12  ; pack_str "space" 32 ]str
and visible_simple_char str = (pack nt_any (fun x-> lowercase_ascii x)) str
and one_char str = (disj named_char visible_simple_char ) str(*char parser doesn't expect spaces between prefix and char*)
and nt_char str =(pack  (caten char_prefix one_char) (fun (_,a) ->Char(a)))str 

and nt_nil str = (pack (caten (skip left_paren) right_paren ) (fun (a,b)-> Nil)) str

and nt_list str = (pack( caten (caten (skip left_paren)  nt_exp ) (skip right_paren)) (fun ((a,b),c) -> b))str 

and nt_lists str = (disj nt_list nt_dot_list )str

and nt_exp str =( pack (star(skip  nt_sexpr))  (fun x -> match x with 
                                                  | [] -> raise X_no_match 
                                                  | a -> List.fold_right(fun a b-> Pair(a,b)) a Nil
                                                  ))str

and nt_dot_list str = (pack( caten (caten (skip left_paren)  nt_exp_2 ) (skip right_paren)) (fun ((a,b),c) -> b))str
and nt_dot str =(pack (caten (char '.') (skip nt_sexpr)) (fun (a,b)-> b) )str
and nt_exp_2 str =( pack  (caten (plus(skip  nt_sexpr)) (nt_dot)) (fun (x,y) -> match x with 
                                                  | [] -> raise X_no_match 
                                                  | a -> (List.fold_right (fun a b-> Pair(a,b)) a y)
                                                  ))str    

and nt_quotes str =disj_list [nt_quoted;nt_qquoted;nt_unquoted_spliced;nt_unquoted] str
and nt_quoted str = (pack(caten   (word "\'")  (skip nt_sexpr ) ) (fun (a,b)-> Pair(Symbol("quote"),Pair( b,Nil)))) str 
and nt_qquoted str =(pack(caten  (pack_char (char '`'))  (skip nt_sexpr ) ) (fun (a,b)->  Pair(Symbol("quasiquote"),Pair( b,Nil)))) str 
and nt_unquoted_spliced str =(pack(caten   (word  ",@") (skip nt_sexpr ) ) (fun (a,b)->  Pair(Symbol("unquote-splicing"),Pair( b,Nil)))) str 
and nt_unquoted str =(pack(caten  (pack_char (char ','))  (skip nt_sexpr )) (fun (a,b)->  Pair(Symbol("unquote"),Pair( b,Nil)))) str 

(*lacks the abillity to check whether there are only one reference*)
and nt_tagged_expr str = (pack(caten (caten (skip nt_tag )  (word "=")   ) (skip nt_sexpr)) (fun ((x,a),b) ->if (check_tag_reference_in_sexp b (get_sexp_match x))
                                                                                                            then TaggedSexpr(get_sexp_match x,b) 
                                                                                                            else raise X_this_should_not_happen))str
and nt_tag_ref str = not_followed_by (pack (caten (caten (word "#{")  (skip nt_symbol)) (word "}")) (fun ((a,b),c) -> TagRef (get_symbol_exp b)) ) (word "=")str
and nt_tag str = pack(caten (caten (word "#{")  (skip nt_symbol)) (word "}") ) (fun ((_,a),_)->a)str

and nt_plmi str = (one_of "+-" )str
and nt_e str = (word_ci "e") str


and s1 str =  ( pack  (caten (pack_char(char '+') ) nt_digit ) (fun (_,x)-> Number(Int(convert_to_num x))))str
and s2 str = ( pack (caten (pack_char(char '-') ) nt_digit ) (fun (_,x)-> Number(Int(-1*convert_to_num x))))str
and s3 str = (pack  nt_digit (fun a-> Number(Int(convert_to_num a))))str
and s4 str =(pack (caten(caten nt_digit (pack_char (char '.'))) nt_digit ) (fun (((a,c),b))-> Number(Float(   get_float_obj a b  ) )))str
and s5 str =(pack (caten(caten (caten reuse_plus_char nt_digit) reuse_dot_char) nt_digit ) (fun ((((a,b),c),d))-> Number(Float(get_float_obj b d))) )str
and s6 str =(pack (caten(caten(caten  reuse_minus_char  nt_digit )reuse_dot_char) nt_digit) (fun ((((a,b),c),d))-> Number(Float(-1.0*.(get_float_obj b d)))) )str
and s7 str =disj_list[s4;s5;s6;s1;s2;s3] str
and s8 str =disj_list[s1;s2;s3] str



and getplusnote2 a b =if b=0 then a else getplusnote2 (a *. 10.0) (b - 1)
and get_minusnote2 a b =if b=0 then a else get_minusnote2 (a /. 10.0) (b + 1)
and get_science_notation2 a b =if b<0 then get_minusnote2 a b else getplusnote2 a b

and getplusnote a b =if b=0 then a else getplusnote (a*10) (b-1)
and get_minusnote a b =if b=0 then a else get_minusnote (a/10) (b+1)
and get_science_notation a b =if b<0 then get_minusnote2 (float_of_int a) b else getplusnote2 (float_of_int a) b
and nt_sce_not str = (pack (caten(caten s7 nt_e) s8) (fun ((a,b),c)-> (match a with 
                                                                        | Number(Int(x))->(match c with 
                                                                            | Number(Int(y))->Number(Float(get_science_notation x y))
                                                                            | _ -> raise X_this_should_not_happen)
                                                                        | Number(Float(x))->(match c with 
                                                                              | Number(Int(y))->Number(Float(get_science_notation2 x y))
                                                                              | _ -> raise X_this_should_not_happen)
                                                                        | _ -> raise X_this_should_not_happen
                                                                        )
                                                       )
                        )str
  
and nt_radix str =disj_list[radix2;radix1]str
and radix1 str =(pack (caten(caten( caten (pack_char (char '#')) nt_digit) (word_ci "r")) (plus radix_nums))
                        (fun (((sulamit,op_base),r),nums)->Number(Int(int_of_float(convert_radix_to_decimal op_base nums))))
                )str
and radix2 str =(pack(caten(caten (caten(caten( caten (pack_char (char '#')) nt_digit) (word_ci "r")) (plus radix_nums)) (pack_char (char '.'))) (plus radix_nums) )
                (fun (((((sulamit,op_base),r),nums),dot),numsdot)->Number(Float(convert_radix_to_float op_base nums numsdot)))
        )str                
and nt_digit str =(plus (range '0' '9'))str;;
let tok_b  = skip  nt_sexpr ;;



module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;
(*read_sexpr doesnt throw exception for more than one sexpr*)
let read_sexpr string = get1 (tok_b (string_to_list string));;

let read_sexprs string = get1 ( (star tok_b) (string_to_list string));;
  
end;; (* struct Reader *)


