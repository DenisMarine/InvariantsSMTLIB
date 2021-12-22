open Printf
open List
open String

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term
 
let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term` et `str_of_test` qui
   convertissent des termes et des tests en chaînes de caractères du
   format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term t =
    match t with
    | Const(n) -> string_of_int n
    | Var(s) -> "x"^string_of_int s
    | Add(t1,t2) -> "("^"+ "^str_of_term t1^" "^str_of_term t2^")"
    | Mult(t1,t2) -> "("^"* "^str_of_term t1^" "^str_of_term t2^")"
;;

let rec str_of_test (t : test) : string = 
	match t with
	| Equals (t1, t2) -> "(= " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
	| LessThan (t1, t2) -> "(< " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
;;	

let str_assertion_cond t =
	match t with
	| Equals (t1, t2) -> "(!= " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
	| LessThan (t1, t2) -> "(>= " ^ str_of_term t1 ^ " " ^ str_of_term t2 ^ ")"
;;

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction str_condition qui prend une liste
   de termes t1, ..., tk et retourne une chaîne de caractères qui
   exprime que le tuple (t1, ..., tk) est dans l'invariant.  Par
   exemple, str_condition [Var 1; Const 10] retourne "(Invar x1 10)".
   *)

let str_condition (l : term list) : string = 
	let t = "(Invar " in
	let rec aux (li : term list) : string =
		if li = [] then "" else
		if tl li = [] then str_of_term (hd li) else
		str_of_term (hd li) ^ " " ^ aux (tl li)
	in t ^ aux l ^ ")"
;;

(* Question 3. Écrire une fonction str_assert_for_all qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^ ")"

let rec liste_sans_doublons liste result =
  if liste = [] then result else 
    try List.find (fun x -> (List.hd liste)=x) result; liste_sans_doublons (List.tl liste) result
    with Not_found -> liste_sans_doublons (List.tl liste) (result@[List.hd liste])
;;
	
let list_of_terms n s =
    let rec aux i ret nbvar =
		if i=length s then ret else
		if nbvar=n then ret else
		if s.[i]='x' then aux (i+1) (ret@[x (int_of_string (make 1 s.[i+1]))]) (nbvar+1)
		else aux (i+1) ret nbvar
    in aux 0 [] 0
;;

let str_assert_forall n s : string =
    let ret = "(forall (" in
    let list = liste_sans_doublons (list_of_terms n s) [] in
    let rec aux l str=
		match l with
		| [] -> str
		| [e] -> str^"("^e^" Int)"^s^")"
		| e::l' -> aux l' (str^"("^e^" Int) ")
    in str_assert (aux list ret)
;;

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let list_of_terms2 n s =
    let rec aux i ret nbvar =
		if i=length s then ret else
		if nbvar=n then ret else
		if s.[i]='x' then 
			let a = int_of_string (make 1 s.[i+1]) in
			aux (i+2) (ret@[Var a]) (nbvar+1)
		else aux (i+1) ret nbvar
    in aux 0 [] 0
;;

let rec str_of_mods l =
	match l with
	| [] -> ""
	| [e] -> str_of_term e
	| e :: l' -> str_of_term e ^ " " ^ str_of_mods l'
;;

let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in
  let s1 = ") (=> (and " ^ str_condition (liste_sans_doublons (list_of_terms2 p.nvars (str_of_mods p.mods)) []) ^ 
		" " ^ str_of_test p.loopcond ^ ") (Invar " ^ str_of_mods p.mods ^ "))" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"
    ^ str_assert_forall p.nvars s1 in
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let s2 = ") (=> (and " ^ str_condition (liste_sans_doublons (list_of_terms2 p.nvars (str_of_mods p.mods)) []) ^
		" " ^ str_assertion_cond p.loopcond ^ ") " ^ str_of_test p.assertion ^ ")" in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^str_assert_forall p.nvars s2 in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]
;;

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}


(*let () = Printf.printf "%s" (smtlib_of_wa p1)*)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

let p2 = {nvars = 2;
		  inits = [(Const 0); (Const 1)];
		  mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1))];
		  loopcond = LessThan ((Var 1), (Const 10));
		  assertion = LessThan ((Var 2), (Const 10))}
		  
let () = Printf.printf "%s" (smtlib_of_wa p2)
