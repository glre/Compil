open Ast
open Parser
open String
open Analyse_statique
(* stdin désigne l'entrée standard (le clavier) *)
(* lexbuf est un canal ouvert sur stdin *)

let ps = print_string
let p x = ps x; print_newline()
let tabulation () = ps "       "

let indenter p = 
  for i = 0 to p do  
    tabulation() 
  done

let rec iterer f = function
  |[] -> ()
  |x::xs -> f x; ps " , "; iterer f xs
;;

exception Caractere_accentue;;

let charge inp = fun s n ->
	let r = input inp s 0 n in
	  for i = 0 to r-1 do
		match s.[i] with
			 c when c >= 'a' && c <= 'z' -> s.[i] <- c
			|c when c >= 'A' && c <= 'Z' -> s.[i] <- char_of_int (int_of_char c - int_of_char 'A' + int_of_char 'a')
			|c when int_of_char c >= 128 -> raise Caractere_accentue
			|c -> s.[i] <- c
		done; r;;



let lexbuf inp = Lexing.from_function (charge inp);;

let parse () = Parser.main Lexer.token (lexbuf stdin);;

let par = parse();;
let ana = Analyse_statique.analyse_statique par;;





let gen = Generation_code_int.transforme_programme ana;;
let viv = Vivacite.vivacite gen;;






let vivopt,k = Optimisation.optimise viv;;
(*let vivopt,k = viv,0;;*)
let code = Generation.genere_code vivopt;;
let tmp = Ast45.transforme_programme vivopt;;

print_string code;;



let a = gen.Ast3.corps.Ast3.fonCode;;
let b = viv.Ast4.principal.Ast4.corps;;

