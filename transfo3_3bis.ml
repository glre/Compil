open Ast3;;
open Ast3bis;;


let transforme_binop = function
    Ast3.Fois -> Ast3bis.Fois
  |Ast3.Plus -> Ast3bis.Plus
  |Ast3.Moins -> Ast3bis.Moins
  |Ast3.Div -> Ast3bis.Div
  |Ast3.Modulo ->  Ast3bis.Modulo
      


  |Ast3.Xor -> Ast3bis.Xor
  |Ast3.Et -> Ast3bis.Et
  |Ast3.Ou -> Ast3bis.Ou
;;

let transforme_uniop = function
    Ast3.Non -> Ast3bis.Non
;;

let transforme_cond = function
  |Ast3.CondEq -> Ast3bis.CondEq
  |Ast3.CondNeq -> Ast3bis.CondNeq
  |Ast3.CondInfEq -> Ast3bis.CondInfEq
  |Ast3.CondSupEq -> Ast3bis.CondSupEq
  |Ast3.CondInf -> Ast3bis.CondInf
  |Ast3.CondSup -> Ast3bis.CondSup
;;

let transforme_sauvegarde = function
    Ast3.Mere(a,b) -> Ast3bis.Mere(a,b)
  |Ast3.IO(i) -> Ast3bis.IO(i)

let transforme_code = function
   Ast3.Read(a) -> Ast3bis.Read(a)
  |Ast3.Affectation_rar(a,b) -> Ast3bis.Affectation_rar(a,b)
  |Ast3.Affectation_ras(a,b) -> Ast3bis.Affectation_ras(a,transforme_sauvegarde b)
  |Ast3.Affectation_sar(a,b) -> Ast3bis.Affectation_sar(transforme_sauvegarde a,b)
  |Ast3.Affectation_rac(a,b) -> Ast3bis.Affectation_rac(a,b)
  |Ast3.Affectation_rat(a,b,c) -> Ast3bis.Affectation_rat(a,b,c)
  |Ast3.Affectation_tar(a,b,c) -> Ast3bis.Affectation_tar(a,b,c)
  |Ast3.Exit -> Ast3bis.Exit
  |Ast3.Affectation_rarf(a,b) -> Ast3bis.Affectation_rarf(a,b)
  |Ast3.Affectation_rfar(a,b) -> Ast3bis.Affectation_rfar(a,b)
  |Ast3.Affectation_addr(a,b,c) -> Ast3bis.Affectation_addr(a,b,c)

  |Ast3.Affectation_unaire(a,b,c)->  Ast3bis.Affectation_unaire(a,b,transforme_uniop c)
  |Ast3.Affectation_binaire(a,b,c,d)->  Ast3bis.Affectation_binaire(a,b,c,transforme_binop d)
  |Ast3.Label(a)-> Ast3bis.Label(a)
  |Ast3.Jump(a) -> Ast3bis.Jump(a)
  |Ast3.CJump(a,b,c,d)-> Ast3bis.CJump(a,b,c,transforme_cond d)
  |Ast3.CJumpb(a,b) -> Ast3bis.CJumpb(a,b)
  |Ast3.WriteString(a)-> Ast3bis.WriteString(a)
  |Ast3.WritelnString(a)-> Ast3bis.WritelnString(a)
  |Ast3.WriteInt(a)-> Ast3bis.WriteInt(a)
  |Ast3.WritelnInt(a)-> Ast3bis.WritelnInt(a)
  |Ast3.AppelProc(a,b,c)-> Ast3bis.AppelProc(a,b,c)
;;

let rec transforme_codelist = function
    [] -> []
  |x::xs -> (transforme_code x)::(transforme_codelist xs)
;;
