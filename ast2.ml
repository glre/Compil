open Hashtbl
open Array

type id = int*int (*0 fonction actuelle, 1 fonction mere, -1 table constante*)

type entier =
  Const_entier of int
 |Fois of entier*entier
 |Plus of entier*entier
 |Moins of entier*entier
 |Div of entier*entier
 |Modulo of entier*entier
 |Variable_entier of id
 |Acces_tableau_entier of id * entier (*id + indice*)
 |Read
 |Adresse of id*entier (*tableau indice *)
 |Dereference_entier of entier  (*ref*)

type booleen =
  Const_booleen of bool
 |Sup of entier*entier
 |Supeq of entier*entier
 |Inf of entier*entier
 |Infeq of entier*entier
 |Eq of entier*entier
 |Neq of entier*entier
 |Et of booleen*booleen
 |Ou of booleen*booleen
 |Non of booleen
 |EqBool of booleen*booleen
 |NeqBool of booleen*booleen
 |Variable_booleen of id
 |Acces_tableau_booleen of id * entier
 |Dereference_booleen of entier  (*ref*)

type code =
  Affectation_entier of id*entier
 |Affectation_booleen of id*booleen

 |Affectation_ref_entier of entier*entier (*ref entier*)
 |Affectation_ref_booleen of entier*booleen (*ref booleen*)
 |Exit
 |Affectation_tae of id*entier*entier     (* Affectation d'un entier à un tableau*)
 |Affectation_tab of id*entier*booleen    (* Affectation d'un booléen à un tableau*)
 |Ifte of booleen*code list*code list (*booleen then else suite*)
 |TantQue of booleen*code list*code list (*valeur vérité, code à exécuter avant chaque itération, corps*)
 |FaitJusquA of code list*booleen
 |Boucle of int*entier*entier*int*code list (*nom variable, debut, fin, increment, corps, suite*)
 |WriteString of int
 |WritelnString of int
 |WriteInt of int
 |WritelnInt of int
 |AppelProc of int list * int list * id list (*(prof,no), liste entier, liste tableau, suite *) 
(*0 soeur, -1 fille, 1 mère, 2 grand mère... -2 général*)

(* writeint 0, writebool 1, writelnint 2, writelnbool 3, exit 4 *)

type fonction = { fonId : int list;
				  fonEnt : int; fonNbEntParam : int;
				  fonTab : int array; fonNbTabParam : int;
				  fonSous_proc : fonction array;
				  fonCode : code list}

type programme = {tableauConsEnt : (int array) array; tableauString : string array; corps : fonction; globale : fonction array}
