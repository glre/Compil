type id_variable = Entier of int|Tableau of (int*int)

(* type registre = RegistreGeneral of int *)

type registre = int

type tableau =   int*int
                
type sauvegarde = RegistreVirtuel of int
		  |RegistreStatique of int
		  |RegistreIO of int
		  |RegistreMere of int*int (*de_combien_on_remonte, no_registre_statique*)
		      
type parametre = ParamStatique of int
                 |ParamVirtuel of int
                 |ParamGeneral of int
        	 |ParamIO of int
		     
type cond = Eq|Neq|SEq|IEq|Sup|Inf
    
type binop = 
    Fois
  |Plus
  |Moins
  |Div
  |Modulo
  |Nor
  |Xor
  |Et
  |Ou
      
type binopi = 
    Addi
  |Andi
  |Xori
  |Ori
      
type uniop =
    Not
  |Neg
      
      
type instruction = 
    Read of int
  |Exit
  |Binop of binop*registre*registre*registre
  |Binopi of binopi*registre*registre*int
  |Uniop of (uniop*registre*registre)
  |Mov of registre*registre
  |Movi of registre*int
  |Movsr of sauvegarde*registre
  |Movrs of registre*sauvegarde
  |Movrt of registre*tableau*registre (*destination, no tableau, indice*)
  |Movtr of tableau*registre*registre (*no_tableau, indice, source*)
      
  |Movrfr of registre*registre
  |Movrrf of registre*registre
  |Movaddr of registre*tableau*registre
      
  |AppelProc of int list*parametre list*tableau list (*id_proc, interdiction de me donner un registre mere, *)
  |Writestring of int (* ne jamais me passer rg 19 *)
  |Writelnstring of int (* ne jamais me passer rg 19 *)
  |Writeint of int (* ne jamais me passer rg 19 *)
  |Writelnint of int (* ne jamais me passer rg 19 *)
  |Jump of int
  |Label of int
  |CJump of int*registre*registre*cond
  |CJumpb of int*registre (*comparaison avec zero*)
      
type fonction = {id : int list;
                 nbRegistreVirtuel : int;
                 nbRegistreStatique : int;
                 nbEntParam : int;
                 nbTablParam : int;
                 tab : int array;
                 filles : fonction array;
                 corps : instruction list;}
    
    
    
type programme = {tableauConsEnt : (int array) array; tableauString : string array; principal : fonction; globale : fonction array}

