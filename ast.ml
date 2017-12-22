type constante =
  ConsInt of int
 |ConsBool of bool
 |ConsCons of string
 |ConsTableau of constante list
 |ConsString of string

type expr =
  Rftoint of expr
 |Inttorf of expr
 |Adresse of expr
 |Dereference of expr
 |ConsExpr of constante
 |Plus of expr*expr
 |Fois of expr*expr
 |Moins of expr*expr
 |Dividende of expr*expr
 |Sup of expr*expr
 |Supeq of expr*expr
 |Inf of expr*expr
 |Infeq of expr*expr
 |Eq of expr*expr
 |Neq of expr*expr
 |Et of expr*expr
 |Ou of expr*expr
 |Non of expr
 |Read
 |Modulo of expr*expr
 |AppelFonc of string*expr list
 |AccesTabl of string*expr list list (*** correction ***)
 |New of expr

type instruction =
  BeginEnd of instruction list
 (*|Affectation of string*expr list list*expr*)
 |Affectation of expr*expr
 |Ifte of expr*instruction*instruction (*booleen then else suite*)
 |TantQue of expr*instruction
 |FaitJusquA of instruction*expr
 |Boucle of string*expr*expr*int*instruction (*nom variable, debut, fin, increment, corps*)
 |AppelProc of string*expr list       (* correction *)
 |Write of expr
 |Writeln of expr
 |Free of expr
 |Exit
 |Vide

type genre =
  Entier
 |Booleen
 |Tableau of (int*int) list*genre
 |String
 |Ref of genre
 |NonSpecifie

type param =
  ParValeur of string*genre     (* correction *)
 |ParAdresse of string*genre    (* correction *)

type declaration =
  DecVar of string*genre
 |DecCons of string*genre*constante
 |DecFonc of string*param list*genre*declaration list*instruction

type programme = declaration

