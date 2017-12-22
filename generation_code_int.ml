open Ast2;;
open Ast3;;
open Array;;
open List;;

let fonction_vide = { Ast3.fonId = [];
		      Ast3.fonLabel = 0;
		      Ast3.variables_mere_utilisees = [];
		      Ast3.variables_utilisees_par_filles = [];
		      Ast3.fonEnt = 0; Ast3.fonNbEntParam = 0;
		      Ast3.fonTab = [||]; Ast3.fonNbTabParam = 0;
		      Ast3.fonSous_proc = [||];
		      Ast3.fonCode = []
		    }
;;


(* taille_entier et taille_bool renvoie le nombre de noeud respectivement d'un entier et d'un booleen, cela nous permet de faire quelques optimisations, notamment lorsque l'on engendre (b1=0 || b2=0), on peut vouloir évaluer le moins couteux d'abord, faire le test, et si pas vérifié seulement, effecuter l'autre test *)
 
let rec taille_entier = function
    Ast2.Const_entier(_) -> 1
  |Ast2.Fois(a,b) -> 1 + (taille_entier a) + (taille_entier b)
  |Ast2.Plus(a,b) -> 1 + (taille_entier a) + (taille_entier b)
  |Ast2.Moins(a,b) -> 1 + (taille_entier a) + (taille_entier b)
  |Ast2.Div(a,b) -> 1 + (taille_entier a) + (taille_entier b)
  |Ast2.Modulo(a,b) -> 1 + (taille_entier a) + (taille_entier b)
  |Ast2.Variable_entier(_) -> 1
  |Ast2.Acces_tableau_entier(i,e) -> 1 + (taille_entier e)
  |Ast2.Adresse(id,e) -> taille_entier e
  |Ast2.Dereference_entier(e) -> taille_entier e
  |Ast2.Read -> 1
;;

let rec taille_bool = function
    Ast2.Const_booleen(_) -> 1
  |Ast2.Sup(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Supeq(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Inf(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Infeq(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Eq(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Neq(e1,e2) -> 1 + (taille_entier e1) + (taille_entier e2) 
  |Ast2.Et(b1,b2) -> 1 + (taille_bool b1) + (taille_bool b2)
  |Ast2.Ou(b1,b2) -> 1 + (taille_bool b1) + (taille_bool b2)
  |Ast2.Non(b) -> 1 + (taille_bool b)
  |Ast2.EqBool(b1,b2) -> 1 + (taille_bool b1) + (taille_bool b2)
  |Ast2.NeqBool(b1,b2) -> 1 + (taille_bool b1) + (taille_bool b2)
  |Ast2.Variable_booleen(_) -> 1
  |Ast2.Acces_tableau_booleen(i,e) -> 1 + (taille_entier e)
  |Ast2.Dereference_booleen(e) -> taille_entier e
;;


(* Le registre de destination de l'entier e est le registre reg. r_reg et r_lbl sont des références sur le nombre de registre et de label déjà créé *)

let rec engendre_entier reg e r_reg r_lbl nbentparam = match e with
    Ast2.Const_entier(i) -> [Ast3.Affectation_rac(reg,i)]
      
  |Ast2.Fois(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier r e1 r_reg r_lbl nbentparam)
      @(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
      @(Ast3.Affectation_binaire(reg,r,r+1,Fois)::[])
      
  |Ast2.Plus(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier r e1 r_reg r_lbl nbentparam)
      @(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
      @(Ast3.Affectation_binaire(reg,r,r+1,Plus)::[])
      
  |Ast2.Moins(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier r e1 r_reg r_lbl nbentparam)
      @(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
      @(Ast3.Affectation_binaire(reg,r,r+1,Moins)::[])
      
  |Ast2.Div(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier r e1 r_reg r_lbl nbentparam)
      @(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
      @(Ast3.Affectation_binaire(reg,r,r+1,Div)::[])
      
  |Ast2.Modulo(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier r e1 r_reg r_lbl nbentparam)
      @(engendre_entier (r+1) e2 r_reg r_lbl nbentparam )
      @(Ast3.Affectation_binaire(reg,r,r+1,Modulo)::[])
	
  |Ast2.Variable_entier((0,i)) when i < nbentparam  -> [Ast3.Affectation_ras(reg,IO(i))]
     
  |Ast2.Variable_entier((0,i))  -> [Ast3.Affectation_rar(reg,i)]
     
  |Ast2.Variable_entier((a,b)) -> [Ast3.Affectation_ras(reg,Mere(a,b))]
     
  |Ast2.Acces_tableau_entier(i,e)-> let r = !r_reg in incr r_reg; 
      (engendre_entier r e r_reg r_lbl nbentparam)
      @[Ast3.Affectation_rat(reg, i,r)] (*id + indice*)
      
  |Ast2.Adresse(id,e) -> let r = !r_reg in incr r_reg; 
      (engendre_entier r e r_reg r_lbl nbentparam)
      @[Ast3.Affectation_addr(reg,id,r)]  (*tableau indice*)
      
  |Ast2.Dereference_entier(e) -> let r = !r_reg in incr r_reg; 
      (engendre_entier r e r_reg r_lbl nbentparam)
      @[Ast3.Affectation_rarf(reg,r)](*ref indice*)

  |Ast2.Read -> [Ast3.Read reg] 
;;

 
(* Pareil que engendre_entier mais pour les booléens *)

let rec engendre_bool reg b r_reg r_lbl nbentparam = match b with

    Ast2.Const_booleen(b) -> if b then [Ast3.Affectation_rac(reg,-1)] else [Ast3.Affectation_rac(reg,0)]

  |Ast2.Sup(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondSup)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)
	  ::[])
      
  |Ast2.Supeq(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondSupEq)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)::[])
      
  |Ast2.Inf(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondInf)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)::[])
      
  |Ast2.Infeq(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam )
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondInfEq)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)::[])
      
  |Ast2.Eq(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondEq)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)::[])
      
  |Ast2.Neq(e1,e2) -> let r = !r_reg in r_reg := !r_reg + 2; 
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	(engendre_entier r e1 r_reg r_lbl nbentparam)
	@(engendre_entier (r+1) e2 r_reg r_lbl nbentparam)
	@(Ast3.CJump(lbl,r,r+1,Ast3.CondNeq)
	  ::Ast3.Affectation_rac(reg,0)
	  ::Ast3.Jump(lbl+1)
	  ::Ast3.Label(lbl)
	  ::Ast3.Affectation_rac(reg,-1)
	  ::Ast3.Label(lbl+1)::[])
      
  |Ast2.Et(b1,b2) -> let r = !r_reg in incr r_reg ;
      let lbl = !r_lbl in r_lbl := !r_lbl + 2; 
	let (t1,t2) = (taille_bool b1,taille_bool b2) in 
	  (engendre_bool r (if t1 < t2 then b1 else b2 ) r_reg r_lbl nbentparam)
	  @[Ast3.CJump(lbl,r,0,CondEq)]
	  @(engendre_bool reg (if t1 < t2 then b2 else b1) r_reg r_lbl nbentparam)
	  @(Ast3.Jump(lbl+1)
	    ::Ast3.Label(lbl)
	    ::Ast3.Affectation_rac(reg,0)
	    ::Ast3.Label(lbl+1)::[])

  |Ast2.Ou(b1,b2) -> let r = !r_reg in r_reg := !r_reg +2; 
      (engendre_bool r b1 r_reg r_lbl nbentparam)
      @(engendre_bool (r+1) b2 r_reg r_lbl nbentparam)
      @[Ast3.Affectation_binaire(reg,r,r+1,Ou)]
	
  |Ast2.Non(b) -> let r = !r_reg in incr r_reg; 
      (engendre_bool r b r_reg r_lbl nbentparam)
      @[Affectation_unaire(reg,r,Non)]
	
  |Ast2.EqBool(b1,b2) ->let r = !r_reg in r_reg := !r_reg +2; 
      (engendre_bool r b1 r_reg r_lbl nbentparam)
      @(engendre_bool (r+1) b2 r_reg r_lbl nbentparam)
      @(Ast3.Affectation_binaire(reg,r,r+1,Ou)
	::Ast3.Affectation_unaire(reg,reg,Non)::[])
      
  |Ast2.NeqBool(b1,b2) -> let r = !r_reg in r_reg := !r_reg +2; 
      (engendre_bool r b1 r_reg r_lbl nbentparam)
      @(engendre_bool (r+1) b2 r_reg r_lbl nbentparam)
      @[Ast3.Affectation_binaire(reg,r,r+1,Xor)]
	
  |Ast2.Variable_booleen((0,i)) when i < nbentparam -> [Ast3.Affectation_ras(reg,IO(i))]
     
  |Ast2.Variable_booleen((0,i))  -> [Ast3.Affectation_rar(reg,i)]
     
  |Ast2.Variable_booleen((a,b)) -> [Ast3.Affectation_ras(reg,Mere(a,b))]
     
  |Ast2.Acces_tableau_booleen(i,e) -> let r = !r_reg in incr r_reg; 
      (engendre_entier r e r_reg r_lbl nbentparam)
      @[Ast3.Affectation_rat(reg,i,r)]
      
  |Ast2.Dereference_booleen(e) -> let r = !r_reg in incr r_reg; 
      (engendre_entier r e r_reg r_lbl nbentparam)
      @[Ast3.Affectation_rarf(reg,r)](*ref indice*)
;;




(* transforme_code linéaire la liste d'instruction contenu dans lcode *)

let rec transforme_code lcode r_reg r_lbl nbentparam= match lcode with
    [] -> []
      
  |Ast2.Affectation_entier((0,i),e)::xs when i< nbentparam -> let reg = !r_reg in incr r_reg; 
      (engendre_entier reg e r_reg r_lbl nbentparam )
      @[(Ast3.Affectation_sar(IO(i),reg))]
      @(transforme_code xs r_reg r_lbl nbentparam) 

  |Ast2.Exit::xs -> Ast3.Exit::(transforme_code xs r_reg r_lbl nbentparam)

  |Ast2.Affectation_entier((0,i),e)::xs -> let reg = !r_reg in incr r_reg; 
      (engendre_entier reg e r_reg r_lbl nbentparam)
      @[(Ast3.Affectation_rar(i,reg))]
      @(transforme_code xs r_reg r_lbl nbentparam) 
      
  |Ast2.Affectation_entier((a,b),e)::xs -> let reg = !r_reg in incr r_reg; 
      (engendre_entier reg e r_reg r_lbl nbentparam)
      @[(Ast3.Affectation_sar(Mere(a,b),reg))]
      @(transforme_code xs r_reg r_lbl nbentparam ) 

  |Ast2.Affectation_booleen((0,i),b)::xs when i<nbentparam -> let reg = !r_reg in incr r_reg; 
      (engendre_bool reg b r_reg r_lbl nbentparam)
      @[(Ast3.Affectation_sar(IO(i),reg))]
      @(transforme_code xs r_reg r_lbl nbentparam)
      
  |Ast2.Affectation_booleen((0,i),b)::xs -> let reg = !r_reg in incr r_reg; 
      (engendre_bool reg b r_reg r_lbl nbentparam)
      @[(Ast3.Affectation_rar(i,reg))]
      @(transforme_code xs r_reg r_lbl nbentparam)


  |Ast2.Affectation_booleen((a,c),b)::xs -> let reg = !r_reg in incr r_reg; 
      (engendre_bool reg b r_reg r_lbl nbentparam)
      @[(Ast3.Affectation_sar(Mere(a,c),reg))]
      @(transforme_code xs r_reg r_lbl nbentparam)


  |Ast2.Affectation_tae(i,e1,e2)::xs -> let reg = !r_reg in r_reg := !r_reg + 2; 
      (engendre_entier reg e1 r_reg r_lbl nbentparam)
      @(engendre_entier (reg+1) e2 r_reg r_lbl nbentparam)
      @[Ast3.Affectation_tar(i,reg,reg+1)]
      @(transforme_code xs r_reg r_lbl nbentparam)

    |Ast2.Affectation_tab(i,e,b)::xs -> let reg = !r_reg in r_reg := !r_reg + 2; 
	(engendre_entier reg e r_reg r_lbl nbentparam )
	@(engendre_bool (reg+1) b r_reg r_lbl nbentparam)
	@[Ast3.Affectation_tar(i,reg,reg+1)]
	@(transforme_code xs r_reg r_lbl nbentparam)

      
    |Ast2.Ifte(b,c2,c1)::xs -> let reg = !r_reg in let lbl = !r_lbl in incr r_reg; r_lbl := !r_lbl +2; 
	((engendre_bool reg b r_reg r_lbl nbentparam)
	 @[(Ast3.CJumpb(lbl,reg))])
	@(transforme_code c1 r_reg r_lbl nbentparam)
	@(Ast3.Jump(lbl+1)::[Ast3.Label(lbl)])
	@(transforme_code c2 r_reg r_lbl nbentparam)
	@(Ast3.Label(lbl+1)
	  ::(transforme_code xs r_reg r_lbl nbentparam))
	

    |Ast2.TantQue(b,c1,c2)::xs -> let reg = !r_reg in incr r_reg; 
	let lbl = !r_lbl in r_lbl := !r_lbl+2; 
	Ast3.Label(lbl)
	  ::(transforme_code c1 r_reg r_lbl nbentparam)
	  @(engendre_bool reg b r_reg r_lbl nbentparam)
	  @Ast3.Affectation_unaire(reg,reg,Non)
	  ::(Ast3.CJumpb(lbl+1,reg)::[])
	  @(transforme_code c2 r_reg r_lbl nbentparam)
	  @(Ast3.Jump(lbl)::Ast3.Label(lbl+1)
	    ::(transforme_code xs r_reg r_lbl nbentparam))


    |Ast2.FaitJusquA(c,b)::xs -> let reg = !r_reg in incr r_reg;  
	let lbl = !r_lbl in incr r_lbl; 
	  (Ast3.Label(lbl)
	   ::(transforme_code c r_reg r_lbl nbentparam))
	  @(engendre_bool reg b r_reg r_lbl nbentparam)
	  @[Ast3.Affectation_unaire (reg,reg,Non);Ast3.CJumpb(lbl,reg)]
	  @(transforme_code xs r_reg r_lbl nbentparam)

    |Ast2.Boucle(i,e1,e2,inc,code)::xs -> let reg = !r_reg in r_reg := !r_reg + 3; 
	let lbl = !r_lbl in r_lbl := !r_lbl + 2;
        (engendre_entier reg e1 r_reg r_lbl nbentparam)
        @(engendre_entier (reg+1) e2 r_reg r_lbl nbentparam)
        @[Ast3.Affectation_rar(i,reg)]
        @[Ast3.Label(lbl)]
        @[Ast3.CJump(lbl+1,i,reg+1,(if inc = 1 then Ast3.CondSup else Ast3.CondInf))]
        @(transforme_code code r_reg r_lbl nbentparam)
        @[Ast3.Affectation_rac(reg +2,inc)]
        @[Ast3.Affectation_binaire(i,i,reg +2,Ast3.Plus)]
        @[Ast3.Jump(lbl)]
        @[Ast3.Label(lbl+1)]
        @(transforme_code xs r_reg r_lbl nbentparam)


	 
    |Ast2.WriteString(entier)::xs -> Ast3.WriteString(entier)::(transforme_code xs r_reg r_lbl nbentparam)
       
    |Ast2.WritelnString(entier)::xs -> Ast3.WritelnString(entier)::(transforme_code xs r_reg r_lbl nbentparam)
       
  |Ast2.WriteInt(e)::xs -> [Ast3.WriteInt(e)]@(transforme_code xs r_reg r_lbl nbentparam)
     
  |Ast2.WritelnInt(e)::xs -> [Ast3.WritelnInt(e)]@(transforme_code xs r_reg r_lbl nbentparam)
     
  |Ast2.AppelProc(i,li,li2)::xs -> Ast3.AppelProc(i,li,li2)::(transforme_code xs r_reg r_lbl nbentparam)
     
     
     
  |Ast2.Affectation_ref_entier(e1,e2)::xs -> let reg = !r_reg in r_reg := !r_reg +2; 
      (engendre_entier (reg) e1 r_reg r_lbl nbentparam)
      @ (engendre_entier (reg+1) e2 r_reg r_lbl nbentparam)
      @ [Ast3.Affectation_rfar(reg,reg+1)]
      @ (transforme_code xs r_reg r_lbl nbentparam)
	
	
  |Ast2.Affectation_ref_booleen(e1,e2)::xs -> let reg = !r_reg in r_reg := !r_reg +2;
      (engendre_entier (reg) e1 r_reg r_lbl nbentparam)
      @ (engendre_bool (reg+1) e2 r_reg r_lbl nbentparam)
      @ [Ast3.Affectation_rfar(reg,reg+1)]
      @ (transforme_code xs r_reg r_lbl nbentparam)
	
;;




let rec transforme_fonction (f : Ast2.fonction) =
  let r_fonEnt = ref f.Ast2.fonEnt in
  let r_label = ref 0 in
  let nbentparam = f.Ast2.fonNbEntParam in
  let nbre_ssproc = Array.length f.Ast2.fonSous_proc in
  let nouveau_ssproc = Array.make nbre_ssproc fonction_vide in
    
    for i = 0 to (nbre_ssproc -1) do
      nouveau_ssproc.(i) <- transforme_fonction f.Ast2.fonSous_proc.(i)
    done;
    let nouveau_code = transforme_code f.Ast2.fonCode r_fonEnt r_label nbentparam in
      
      { Ast3.fonId = f.Ast2.fonId ; 
	Ast3.fonLabel = !r_label;
	Ast3.variables_mere_utilisees = [];
	Ast3.variables_utilisees_par_filles = [];
	Ast3.fonEnt = !r_fonEnt; Ast3.fonNbEntParam = f.Ast2.fonNbEntParam;
	Ast3.fonTab = f.Ast2.fonTab; Ast3.fonNbTabParam = f.Ast2.fonNbTabParam;
	Ast3.fonSous_proc = nouveau_ssproc;
	Ast3.fonCode = nouveau_code
      }
;;


(* La génération de code est désormais finis, il n'y a plus qu'à décorer les fonctions des variables utilisées par la fonction courante (variables_mere_utilisees) et par les fonctions filles (variables_utilisees_par_filles) *)



(* Renvoie les variables de la fonction courante utilisée dans le code *)
(* C'est juste un parcours de la liste d'instruction *)
let rec varuse_mere (code_mere : Ast3.code list) acc = match code_mere with
    [] -> acc
  |Ast3.Affectation_rar(r1,r2)::xs -> varuse_mere xs (r1::r2::acc) 
  |Ast3.Affectation_ras(r,_)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_sar(_,r)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_rac(r,_)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_rat(r,_,_)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_tar(_,_,r)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_unaire(r,_,_)::xs -> varuse_mere xs (r::acc)
  |Ast3.Affectation_binaire(r1,r2,r3,_)::xs -> varuse_mere xs (r1::r2::r3::acc)
  |Ast3.CJump(_,r1,r2,_)::xs -> varuse_mere xs (r1::r2::acc)
  |Ast3.CJumpb(_,r)::xs -> varuse_mere xs (r::acc)
  |Ast3.WriteInt(r)::xs ->  varuse_mere xs (r::acc)
  |Ast3.WritelnInt(r)::xs ->  varuse_mere xs (r::acc)
  |Ast3.AppelProc(_,l,_)::xs ->  varuse_mere xs (l@acc)
  |x::xs -> varuse_mere xs acc
;;


(* Pour les variables utilisées par les fonctions filles, on parcoure brutalement pour toutes les fonctions, toutes les filles (avec leur profondeur par rapport à leur mère, on regarde leur code et on ajoute les variables qui sont utilisées de la mère à la bonne profondeur) *)


(* prend une fonction et une profondeur et renvoie la liste des indices des registres utilisé d'un mère profondeur fois plus haut.*)
let var_used_filles_aux (fille : Ast3.fonction) prof =
  let c = fille.Ast3.fonCode in
  let rec aux code acc = match code with
      [] -> acc 
    |Ast3.Affectation_ras(_,Mere(i,p))::xs when i = prof ->(aux xs (p::acc))
       
    |Ast3.Affectation_sar(Mere(i,p),_)::xs when i = prof -> (aux xs (p::acc))
       
    |x::xs -> (aux xs acc)
  in
    aux c []
;;



(* A une fonction renvoie les var utilisé par les filles *)
let rec var_used_filles (f : Ast3.fonction) prof = 
  let ssproc = f.Ast3.fonSous_proc in
  let nb = Array.length ssproc in
  let l = ref [] in
    
    l := (var_used_filles_aux f prof);
    
    for i = 0 to (nb-1) do
      let l1 = var_used_filles ssproc.(i) (prof+1) in
       	l := !l @ l1;
    done;
    !l
;;

let rec supprimer_doublons l1 = match l1 with
    [] -> []
  |x::xs -> if (List.mem x xs) then supprimer_doublons xs else x::(supprimer_doublons xs)
;;



let rec ajoute_varuse (f : Ast3.fonction) = 
  let ssproc = f.Ast3.fonSous_proc in
  let nb = Array.length ssproc in
  let l = ref [] in
    for i = 0 to (nb-1) do
      l := !l @ (var_used_filles ssproc.(i) 1);
    done;
    
    
    
    for i = 0 to (nb-1) do
      ssproc.(i) <- (ajoute_varuse ssproc.(i))
    done;
    
    { Ast3.fonId = f.Ast3.fonId ; 
      Ast3.fonLabel = f.Ast3.fonLabel;
      Ast3.variables_mere_utilisees = supprimer_doublons (varuse_mere f.Ast3.fonCode []);
      Ast3.variables_utilisees_par_filles = supprimer_doublons !l ;
      Ast3.fonEnt = f.Ast3.fonEnt; Ast3.fonNbEntParam = f.Ast3.fonNbEntParam;
      Ast3.fonTab = f.Ast3.fonTab; Ast3.fonNbTabParam = f.Ast3.fonNbTabParam;
      Ast3.fonSous_proc = ssproc;
      Ast3.fonCode = f.Ast3.fonCode
    }
;;

let transforme_programme (p : Ast2.programme) =
  {Ast3.tableauConsEnt = p.Ast2.tableauConsEnt; Ast3.tableauString = p.Ast2.tableauString; Ast3.corps = (ajoute_varuse (transforme_fonction p.Ast2.corps)); Ast3.globale = Array.map (fun s -> ajoute_varuse (transforme_fonction s)) p.Ast2.globale}
;;
