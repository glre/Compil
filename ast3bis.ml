open Hashtbl
open Array

type id = int*int (*0 fonction actuelle, 1 fonction mere, -1 table constante*)

type binop =
  Fois
 |Plus
 |Moins
 |Div
 |Modulo


 |Xor
 |Et
 |Ou

type uniop =
 |Non

type entier =
  Const_entier of int
 |Variable_entier of id
 |Acces_tableau_entier of id * entier (*id + indice*)

type cond =
 |CondEq
 |CondNeq
 |CondInfEq
 |CondSupEq
 |CondInf
 |CondSup

type sauvegarde = Mere of (int*int) (* de combien on remonte, et le numéro *)
                  |IO of int

type code =
    Affectation_rar of int*int 
  |Affectation_ras of int*sauvegarde
  |Affectation_sar of sauvegarde*int
  |Affectation_rac of int*int (*entier, constante*)
  |Affectation_rat of int*id*int (*entier,tableau,indice*)
  |Affectation_tar of id*int*int (*tableau,indice,entier*)

  |Affectation_rarf of int*int (*entier,ref*)
  |Affectation_rfar of int*int (*ref,entier*)
  |Affectation_addr of int*id*int (*ref,tableau,indice*)

  |Affectation_unaire of int*int*uniop
  |Affectation_binaire of int*int*int*binop
  |Read of int
  |Exit
  |Label of int
  |Jump of int
  |CJump of int*int*int*cond (*lbl; r1; r2 *)
  |CJumpb of int*int
  |WriteInt of int
  |WritelnInt of int
  |WriteString of int
  |WritelnString of int
  |AppelProc of int list * int list * id list (*(prof,no), liste entier, liste tableau, suite *) (*0 soeur, -1 fille, 1 mère, 2 grand mère... -2 général*)

(* writeint 0, writebool 1, writelnint 2, writelnbool 3, exit 4 *)

type fonction = { fonId : int list;
		  fonLabel : int;
		  fonEnt : int; fonNbEntParam : int;
		  variables_mere_utilisees : int list;
		  variables_utilisees_par_filles : int list;
		  fonTab : int array; fonNbTabParam : int;
		  fonSous_proc : fonction array;
		  fonCode : code list;
		  nb_registes_statiques : int;
		  fonColoration : int array}

type programme = {tableauConsEnt : (int array) array; tableauString : string array; corps : fonction; globale : fonction array}
