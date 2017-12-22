(*#load "graph.cma";;
#load "transfo3_3bis.cmo";;*)
open Ast3;;
open Ast3bis;;
open Ast4;;
open Graph;;
open Graph.Pack.Graph;;
  
module C = Graph.Coloring.Mark (Graph.Pack.Graph);;


(******** Fonctions utiles pour débugger, notamment les problèmes de Not_found pour les tables de hachage ************)

let print_espace = fun n -> for i = 1 to n do Printf.printf " "; done;;
let pi = fun i x -> print_espace i; print_int x; Printf.printf "\n";;
let hash_to_list h = Hashtbl.fold (fun a b c -> (a,b)::c) h []
let rec print_list i = fun pr l -> 
  let rec aux = fun l -> match l with
      [] -> print_espace i; Printf.printf "[]\n"
    |[a] -> pr a; print_espace i; Printf.printf "\n"
    |(a::r) -> pr a; aux r in aux l;;

let print_couple i = fun pr1 pr2 (a,b) -> print_espace i; Printf.printf "(\n"; pr1 a; pr2 b; print_espace i; Printf.printf ")\n";;

exception Entier of int
exception Bizarre of (int list* (int * int) list) list * int list
  
let hashfind = fun no h x -> try Hashtbl.find h x with Not_found -> raise (Entier no)
let hashfind2 = fun h id oldid-> try Hashtbl.find h id with Not_found -> let l = hash_to_list h in let c= (List.map (fun (a,b) -> a,(hash_to_list b)) l),(id,oldid) in print_couple 0 (print_list 1 (print_couple 2 (print_list 3 (pi 4)) (print_list 3 (print_couple 4 (pi 5) (pi 5))))) (print_couple 4 (print_list 5 (pi 6)) (print_list 5 (pi 6))) c; raise (Entier 2);;


(********************* Fin des fonctions de débug *************************)



(* On crée le graphe de flot de contrôle *)
(* Définition des structures *)
type noeud = {mutable use : int list; mutable def : int list; mutable entrant : int list; mutable sortant : int list; mutable succ : int list };;
type graphe_flot = noeud array;;


let noeud_vide = {use = []; def = []; entrant = []; sortant = []; succ = []};;

let pratique l1 l2 p = match l1 with
  |[] -> l2
  |_ -> (p+1)::l2
;;

(* Permet de construire le graphe, on matche chaque instruction et on dit ce qui est use, def, et les successeurs pour chaque noeud du graphe de flot de contrôle *)
let construire_graphe code nb_label =  
  let l = List.length code in
  let graphe = Array.make l noeud_vide in
  let label = Array.make nb_label 0 in
    for i = 0 to (l-1) do
      graphe.(i) <- {use = []; def = []; entrant = []; sortant = []; succ = []}
    done;
    

(* On parcoure chaque instruction en regardant quels registres est def ou use, et quels sont les successeurs de cette instruction *)
    
    let rec initialisation c p = match c with
	[] -> ()
    |Ast3.Exit::xs -> graphe.(p).use <- []; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Read(i1)::xs -> graphe.(p).use <- []; graphe.(p).def <- [i1]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_rar(i1,i2)::xs -> graphe.(p).use <- [i2]; graphe.(p).def <- [i1]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_ras(i,s)::xs -> graphe.(p).use <- []; graphe.(p).def <- [i]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_sar(s,i)::xs -> graphe.(p).use <- [i]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_rac(i,c)::xs -> graphe.(p).use <- []; graphe.(p).def <- [i]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_rat(i,_,ind)::xs -> graphe.(p).use <- [ind]; graphe.(p).def <- [i]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_tar(_,ind,i)::xs -> graphe.(p).use <- [i;ind]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_unaire(i1,i2,_)::xs -> graphe.(p).use <- [i2]; graphe.(p).def <- [i1]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_binaire(i1,i2,i3,_)::xs -> graphe.(p).use <- [i2;i3]; graphe.(p).def <- [i1]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Label(i)::xs -> label.(i) <- p; graphe.(p).use <- []; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Jump(i)::xs -> graphe.(p).use <- []; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- label.(i)::(pratique xs [] p);initialisation xs (p+1)
	
    |Ast3.CJump(lbl,r1,r2,_)::xs -> graphe.(p).use <- [r1;r2]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- label.(lbl)::(pratique xs [] p);initialisation xs (p+1)
	
    |Ast3.CJumpb(lbl,r)::xs -> graphe.(p).use <- [r]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- label.(lbl)::(pratique xs [] p);initialisation xs (p+1)
	
    |Ast3.WriteInt(reg)::xs -> graphe.(p).use <- [reg]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p);initialisation xs (p+1)
	
    |Ast3.WritelnInt(reg)::xs ->  graphe.(p).use <- [reg]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p);initialisation xs (p+1)
	
    |Ast3.WriteString(_)::xs -> graphe.(p).use <- []; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
 
    |Ast3.WritelnString(_)::xs -> graphe.(p).use <- []; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.AppelProc(_,l,_)::xs -> graphe.(p).use <- l; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_rarf(a,b)::xs -> graphe.(p).use <- [b]; graphe.(p).def <- [a]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_rfar(a,b)::xs -> graphe.(p).use <- [a;b]; graphe.(p).def <- []; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
    |Ast3.Affectation_addr(a,id,b)::xs -> graphe.(p).use <- [b]; graphe.(p).def <- [a]; graphe.(p).entrant <- []; graphe.(p).sortant <- []; graphe.(p).succ <- (pratique xs [] p); initialisation xs (p+1)
	
	
    in
      
      initialisation code 0;
      graphe
;;
(********** Utilitaire**********)

(* retourne l1 privé de l2 *)
let rec prive l1 l2 = match l1 with
  |[] -> []
  |x::xs -> if List.mem x l2 then prive xs l2 else x::(prive xs l2)
;;

let rec supprimer_doublons l1 = match l1 with
    [] -> []
  |x::xs -> if (List.mem x xs) then supprimer_doublons xs else x::(supprimer_doublons xs)
;;

(******** Fin de l'entracte utilitariste ***********)

(* On Applique l'algorithme du point_fixe pour savoir ce qui est in et out à chaque noeud du graphe *)
let point_fixe graphe = 
  let l = Array.length graphe in
  let temoin = ref false in
  let entrant_temp = ref [] in
  let sortant_temp = ref [] in
  let rec super_union_in l_succ = match l_succ with
      [] -> []
    |x::xs -> graphe.(x).entrant@(super_union_in xs)
  in
    while (!temoin = false) do
      temoin := true ;
      for i = (l-1) downto 0 do
	entrant_temp := graphe.(i).entrant ;
	sortant_temp := graphe.(i).sortant ;
	graphe.(i).entrant <-   List.sort (let f x y = x-y in f) (supprimer_doublons (graphe.(i).use @ (prive graphe.(i).sortant graphe.(i).def))) ;
	graphe.(i).sortant <-  List.sort (let f x y = x-y in f) (supprimer_doublons (super_union_in graphe.(i).succ));
	if (graphe.(i).entrant <> (!entrant_temp)) || (graphe.(i).sortant <> (!sortant_temp)) then temoin := false else ();
      done;
    done;
    graphe
;;


(************** Création du graphe d'interférence *******************)

let graphe_interference code nb_lbl nb_reg  = 
  let g1 = point_fixe ( construire_graphe code nb_lbl ) in
  let g2 = Graph.Pack.Graph.create ()in
  let sommets = Array.make nb_reg (V.create (-1)) in
    for i = 0 to (nb_reg -1) do
      sommets.(i) <- V.create i;
      add_vertex g2 sommets.(i);
      Graph.Pack.Graph.Mark.set sommets.(i) 0;
    done;
    
    let rec aux2 x xs = match xs with
	[] -> ()
      |y::ys -> add_edge g2 sommets.(x) sommets.(y); aux2 x ys
    in
      
    let rec aux liste = match liste with
	[] -> ()
      |x::xs -> aux2 x xs; aux xs
    in
      
      for j = 0 to ((Array.length g1) -1) do
	aux g1.(j).entrant; aux g1.(j).sortant
      done;
      
      sommets,g2
;;  (* On renvoit le tableau des sommets et le graphe g2 qui a été construit*)


let get_coloration sommets graphe nombre =
  let l = Array.length sommets in
  let coloration = Array.make l 0 in
    C.coloring graphe nombre;
    for i = 0 to (l -1) do
      coloration.(i) <- Graph.Pack.Graph.Mark.get sommets.(i)
    done;
    coloration;;

(* Renvoie une table de coloration des registres t.(i) est la couleur du ième registre virtuel *)

(* Prend une fonction et récupère une coloration, c'est à dire un tableau *)
let get_coloration_f (f : Ast3.fonction) =
  let s_t,g_t = graphe_interference f.Ast3.fonCode f.Ast3.fonLabel f.Ast3.fonEnt in
    get_coloration s_t g_t (f.Ast3.fonEnt+1)
;;

(************ Fin de l'analyse de vivacite *****************)



(************ Début de l'allocation ***********************)

(* Première passe, on crée la table de hachage pour les registres statiques et on transforme l'ast3 en ast3bis *)

(* Table de hachage dont les éléments sont des tables de hachages, une pour chaque fontion *)
(* Les clés sont des liste d'entier qui identifient les fonctions et à qui on associe des tables de hachage. Ces tables étant de type (int,int), et qui nous servent pour associer à certain registre un registre statique. Exemple si (4,0) appartient à une table de hachage, alors cela signifie qu'au registre 4 est associé le registre statique 0 *) 

(* Le code n'est pas très heureux en notation ici *)
let creer_hashtbl (p : Ast3.programme) =
  
  let t_h = Hashtbl.create 10 in
  let f = p.Ast3.corps in
    
  let rec aux f hashtbl =
    let id_f = f.Ast3.fonId in
    let var_use_filles = f.Ast3.variables_utilisees_par_filles in
    let regs = Hashtbl.create (List.length var_use_filles) in
      
    let ss_fonctions = f.Ast3.fonSous_proc in
      
    let rec aux2 h p l = match l with
	[] -> ()
      |x::xs -> Hashtbl.add h x p; aux2 h (p+1) xs
    in
      
      aux2 regs 0 var_use_filles;
      Hashtbl.add t_h (id_f) regs;
      
      for i = 0 to ((Array.length ss_fonctions) -1) do
	aux ss_fonctions.(i) t_h;
      done;
  in
    aux f t_h;
    
    for i = 0 to (Array.length p.Ast3.globale)-1 do
      aux (p.Ast3.globale.(i)) t_h;
    done;
    
    t_h;;      


let fonction_vide = { Ast3bis.fonId = [] ;
		      Ast3bis.fonLabel = 0;
		      Ast3bis.variables_mere_utilisees = [];
		      Ast3bis.variables_utilisees_par_filles = [];
		      Ast3bis.fonEnt = 0; Ast3bis.fonNbEntParam = 0;
		      Ast3bis.fonTab = [||]; Ast3bis.fonNbTabParam = 0;
		      Ast3bis.fonSous_proc = [||];
		      Ast3bis.fonCode = [];
		      Ast3bis.nb_registes_statiques = 0;
		      Ast3bis.fonColoration = [||]		    
		    }
;;


(* transforme_fonction3_3bis transforme un Ast3 en Ast3bis, c'est à dire en exactement la même structure sauf que chaque fonction est décoré de la coloration de ses registres *)

let rec transforme_fonction3_3bis (f : Ast3.fonction) =
  let l = (Array.length f.Ast3.fonSous_proc) in
  let tab = Array.make l fonction_vide in
    for i = 0 to (l-1) do
      tab.(i) <- transforme_fonction3_3bis f.Ast3.fonSous_proc.(i)
    done;
    
    {Ast3bis.fonId = f.Ast3.fonId; 
     Ast3bis.fonLabel = f.Ast3.fonLabel;
     Ast3bis.fonEnt = f.Ast3.fonEnt; Ast3bis.fonNbEntParam = f.Ast3.fonNbEntParam;
     Ast3bis.variables_mere_utilisees = f.Ast3.variables_mere_utilisees;
     Ast3bis.variables_utilisees_par_filles = f.Ast3.variables_utilisees_par_filles;
     Ast3bis.fonTab = f.Ast3.fonTab; Ast3bis.fonNbTabParam = f.Ast3.fonNbTabParam;
     Ast3bis.fonSous_proc = tab;
     Ast3bis.fonCode = (Transfo3_3bis.transforme_codelist f.Ast3.fonCode);
     Ast3bis.nb_registes_statiques = (List.length f.Ast3.variables_utilisees_par_filles);
     Ast3bis.fonColoration =  get_coloration_f f
    }
;;


let transforme_programme3_3bis (p: Ast3.programme) =
  { Ast3bis.tableauConsEnt = p.Ast3.tableauConsEnt; Ast3bis.tableauString = p.Ast3.tableauString; Ast3bis.corps = (transforme_fonction3_3bis p.Ast3.corps); Ast3bis.globale = Array.map transforme_fonction3_3bis p.Ast3.globale }
;;


(* Les Choses sérieuses commencent *)
(*  Maintenant on a tous les élements pour générer l'ast4 (normalement...!) *)



let fvide4 = {Ast4.id = [];
              Ast4.nbRegistreVirtuel = 0;
              Ast4.nbRegistreStatique = 0;
                 Ast4.nbTablParam = 0;
                 Ast4.nbEntParam = 0;
                 Ast4.tab = [||];
                 Ast4.filles = [||];
                 Ast4.corps = []
	     };;

(* Récupère le max d'un tableau *)
let max t =
  let l = Array.length t in
    if l = 0 then 0 else
      begin
	let m = ref t.(0) in
	  for i = 1 to (l-1) do
	    if t.(i) > (!m) then m := t.(i) else ()
	  done;
	  (!m)
      end
;;

let cond3to4 cond= match cond with
  |Ast3bis.CondEq -> Ast4.Eq
  |Ast3bis.CondNeq -> Ast4.Neq
  |Ast3bis.CondInfEq -> Ast4.IEq
  |Ast3bis.CondSupEq -> Ast4.SEq
  |Ast3bis.CondInf -> Ast4.Inf
  |Ast3bis.CondSup -> Ast4.Sup
;;




let convertir_binop op = match op with
    Ast3bis.Fois -> Ast4.Fois
  |Ast3bis.Plus -> Ast4.Plus
  |Ast3bis.Moins -> Ast4.Moins
  |Ast3bis.Div -> Ast4.Div
  |Ast3bis.Modulo -> Ast4.Modulo
     
     
  |Ast3bis.Xor -> Ast4.Xor
  |Ast3bis.Et -> Ast4.Et
  |Ast3bis.Ou -> Ast4.Ou
;;

exception CoupeListe


(* Cette fonction est une relique d'un passé plus glorieux *)
let rec transformer_liste_tableau nb_tab_param = function
  |l -> l
;;



let sauvegarde_pile ref_virtuels = 
  let rec aux e reference= match e with
      0 -> []
    |p -> incr reference; Ast4.Movsr(Ast4.RegistreVirtuel(!ref_virtuels -1),p)::(aux (p-1) reference )
  in
    aux 17 ref_virtuels
;;


(* prive la liste de ses p premier éléments *) 
let couper_liste = fun liste2 l2 ->
  let rec couper_liste_aux liste l = match liste,l with
    |liste,0 -> liste
    |x::xs,l -> (couper_liste_aux xs (l-1))
    |[],_ -> failwith "inconsistance vivacite"
  in
    couper_liste_aux liste2 l2
;;


(* Les registres temporaires sont 17-18-19 *)

let rec transforme_instr (c : Ast3bis.code list) id h_t color varused nb_ent_param nb_tab_param ref_virtuels =
(* récupère et actualise sont utilisées par cette version, qui est une version patché de dernières minute *)

  (* Récupère permet de récupérer le registre reg dans le registre temporaire dest. Elle match si reg est un registre statique, un registre virtuel ou un registre réel *)  
  let recupere  = fun dest reg ->
    let f = hashfind2 h_t id id in
      match reg with
	  r when (Hashtbl.mem f r) -> [Ast4.Movrs(dest,Ast4.RegistreStatique(Hashtbl.find f reg))]
	|r when color.(r) > 16 -> [Ast4.Movrs(dest,Ast4.RegistreVirtuel(color.(r)-17))]
	|r -> [Ast4.Mov(dest,color.(r)-1)]
  in


(* Actualise met à jour le registre reg par rapport à la source, en matchant si reg est un registre statique, virtuel ou réel *)
    
  let actualise = fun reg source -> match reg with
      r when (List.mem r varused) -> let  ht2 = Hashtbl.find h_t id in [Ast4.Movsr(Ast4.RegistreStatique(Hashtbl.find ht2 reg),source)]
    |r when color.(r) > 16 -> [Ast4.Movsr(Ast4.RegistreVirtuel(color.(r)-17),source)]
    |r -> [Ast4.Mov(color.(r)-1,source)]
  in
    
  let transformer_reg id h_t varused liste_reg color=
    let f = hashfind2 h_t id id in
    let rec aux = function
      |[] -> []
      |x::xs when x< nb_ent_param -> Ast4.ParamIO(x)::(aux xs)
      |x::xs when Hashtbl.mem f x -> Ast4.ParamStatique(hashfind 3 f x)::(aux xs)
      |x::xs when color.(x) <= 16 -> Ast4.ParamGeneral(color.(x)-1)::(aux xs)
      |x::xs -> Ast4.ParamVirtuel(color.(x)-17)::(aux xs)
    in
      aux liste_reg
  in

(* On engendre chaque instruction, en tenant cette fois ci en compte de l'allocation de registres, i.e si ce sont des registre réels, virtuels, statique, IO, ou encore Mere *)

    match c with
	
	[] -> []
	  
      |Ast3bis.Read(i)::xs -> [Ast4.Read 17]
	 @(actualise i 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	    
      |Ast3bis.CJumpb(lbl,i)::xs -> (recupere 17 i)
	 @[Ast4.CJumpb(lbl,17)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	    
      |Ast3bis.CJump(lbl,i1,i2,cond)::xs -> (recupere 17 i1)
	 @(recupere 18 i2)
	 @[Ast4.CJump(lbl,17,18,cond3to4 cond)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	    
      |Ast3bis.Affectation_rar(i1,i2)::xs -> (recupere 17 i2)
	 @(actualise i1 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	    
      |Ast3bis.Affectation_ras(i,Ast3bis.IO(s))::xs -> [Ast4.Movrs(17,Ast4.RegistreIO(s))]
	 @(actualise i 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	 
      |Ast3bis.Affectation_sar(Ast3bis.IO(s),i)::xs -> (recupere 17 i)
	 @[Ast4.Movsr(Ast4.RegistreIO(s),17)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	 
      |Ast3bis.Affectation_ras(i,Ast3bis.Mere(a,b))::xs -> let ht2 = Hashtbl.find h_t (couper_liste id a) in 
	  [Ast4.Movrs(17,Ast4.RegistreMere(a,Hashtbl.find ht2 b))]
	  @(actualise i 17)
	  @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
													       
      |Ast3bis.Affectation_sar(Ast3bis.Mere(a,b),i)::xs -> let ht2 = Hashtbl.find h_t (couper_liste id a) in 
	  (recupere 17 i)
	  @[Ast4.Movsr(Ast4.RegistreMere(a,Hashtbl.find ht2 b),17)]
	  @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
													    
      |Ast3bis.Exit::xs -> Ast4.Exit::(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

      |Ast3bis.Affectation_rac(i,c)::xs -> [Ast4.Movi(17,c)]
	 @(actualise i 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
      
      |Ast3bis.Affectation_rat(i,(i1,i2),ind)::xs -> (recupere 17 ind)
	 @[Ast4.Movrt(17,(i1,i2),17)]
	 @(actualise i 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

      |Ast3bis.Affectation_tar((i1,i2),ind,i)::xs -> (recupere 17 i)
	 @(recupere 18 ind)
	 @[Ast4.Movtr((i1,i2),18,17)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
      
      |Ast3bis.Affectation_unaire(i1,i2,Ast3bis.Non)::xs -> (recupere 17 i2)
	 @[Ast4.Uniop (Not,17,17)]
	 @(actualise i1 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

      |Ast3bis.Affectation_binaire(i1,i2,i3,bino)::xs -> (recupere 17 i2)
	 @(recupere 18 i3)
	 @[Ast4.Binop ((convertir_binop bino),17,17,18)]
	 @(actualise i1 17)
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)      

      |Ast3bis.Label(i)::xs -> Ast4.Label(i)
	 ::(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
       
      |Ast3bis.Jump(i)::xs -> Ast4.Jump(i)
	 ::(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
       

      |Ast3bis.WriteString(i)::xs -> Ast4.Writestring(i)
	 ::(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
      
      |Ast3bis.WritelnString(i)::xs -> Ast4.Writelnstring(i)
	 ::(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

      |Ast3bis.WriteInt(i)::xs -> (recupere 17 i)
	 @[Ast4.Writeint(17)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

      |Ast3bis.WritelnInt(i)::xs -> (recupere 17 i)
	 @[Ast4.Writelnint(17)]
	 @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)


    |Ast3bis.AppelProc(id2,liste_reg,id_list)::xs -> let liste = transformer_reg id h_t varused liste_reg color in 
	[Ast4.AppelProc(id2,liste, transformer_liste_tableau nb_tab_param id_list)]
	@(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
	  

    |Ast3bis.Affectation_rarf(r1,r2)::xs -> (recupere 17 r2)
       @[Ast4.Movrrf(17,17)]
       @(actualise r1 17)
       @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)
       
    |Ast3bis.Affectation_rfar(r1,r2)::xs -> (recupere 18 r2)
       @(recupere 17 r1)
       @[Ast4.Movrfr(17,18)]
       @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)

    |Ast3bis.Affectation_addr(a,id2,b)::xs -> (recupere 17 b)
       @[Ast4.Movaddr(17,id2,17)]
       @(actualise a 17)
       @(transforme_instr xs id h_t color varused nb_ent_param nb_tab_param ref_virtuels)



;;

(********************Fonction utiles pour les cally_save *************************)
(* Regarde quels registres sont des registres réels dans une liste de registre virtuels issue de l'ast3 *)

let rec vrais_registres_used liste acc color= match liste with
  |[] -> acc
  |x::xs when color.(x) > 16 -> vrais_registres_used xs acc color
  |x::xs -> vrais_registres_used xs (if List.mem color.(x) acc then acc else (color.(x)::acc)) color
;;

(* Routines pour sauvegarder ou remettre à jour des registres cally save *)

let rec cally_save_entree liste_var_use nb p = match liste_var_use with
  |[] -> []
  |x::xs -> Ast4.Movsr(Ast4.RegistreVirtuel(nb+p),x-1)::(cally_save_entree xs nb (p+1))
;;

let rec cally_save_sortie liste_var_use nb p = match liste_var_use with
  |[] -> []
  |x::xs -> Ast4.Movrs(x-1,Ast4.RegistreVirtuel(nb+p))::(cally_save_sortie xs nb (p+1))
;;

(****************** Fin fonction utiles pour les cally save ***********************)


(* transforme une Ast3bis.fonction avec l'aide de transforme_instr,cela correspond à l'allocation de registre *)

let rec transforme_fonction_3bisto4 (f : Ast3bis.fonction) h_t =
  let nb_filles = Array.length f.Ast3bis.fonSous_proc in
  let nouvelles_filles = Array.make nb_filles fvide4 in
  let varuse = f.Ast3bis.variables_utilisees_par_filles in
  let nb_tab_param = f.Ast3bis.fonNbTabParam in
  let nb_ent_param = f.Ast3bis.fonNbEntParam in
    
    for i = 0 to (nb_filles -1) do
      nouvelles_filles.(i) <- transforme_fonction_3bisto4 f.Ast3bis.fonSous_proc.(i) h_t
    done;
    
    let coloration = f.Ast3bis.fonColoration in
      
    (* Ici on dit qu'on utilise 16 registres, donc ce qui a été coloré avec n>16 sera des registres virtuels *)
    (* Les vraies registres utilisées pour le calcul sont 8 - (8+nbre_reg) *)
      
    let nbre_reg = 16 in
    let max_color = max coloration in
    let nbre_reg_virt = (if (max_color-1 - nbre_reg) < 0 then 0 else (max_color-1 - nbre_reg)) in
    let nb_reg_virtuel = ref nbre_reg_virt in
    let liste_var_used = vrais_registres_used (f.Ast3bis.variables_mere_utilisees) [] coloration in
    let nbre_var_used = List.length liste_var_used in
      
    let corps_new = (cally_save_entree liste_var_used nbre_reg_virt 0)@(transforme_instr f.Ast3bis.fonCode f.Ast3bis.fonId h_t coloration varuse nb_ent_param nb_tab_param nb_reg_virtuel)@(cally_save_sortie liste_var_used nbre_reg_virt 0) in
      
      
      {Ast4.id = f.Ast3bis.fonId;
       Ast4.nbRegistreVirtuel = nbre_reg_virt+nbre_var_used;
       Ast4.nbRegistreStatique = (List.length f.Ast3bis.variables_utilisees_par_filles);
       Ast4.nbTablParam = f.Ast3bis.fonNbTabParam;
       Ast4.nbEntParam = f.Ast3bis.fonNbEntParam;
       Ast4.tab = f.Ast3bis.fonTab;
       Ast4.filles = nouvelles_filles;
       Ast4.corps = corps_new
      }
;;



let transforme_programme_3bisto4 (p : Ast3bis.programme) h_t = 
  { Ast4.tableauConsEnt = p.Ast3bis.tableauConsEnt; Ast4.tableauString = p.Ast3bis.tableauString; Ast4.principal = transforme_fonction_3bisto4 p.Ast3bis.corps h_t; Ast4.globale = Array.map (fun x -> transforme_fonction_3bisto4 x h_t) p.Ast3bis.globale}
;;


(* phase d'optimisation, pour l'instant, on supprime juste les r1 <- r1, histoire d'élaguer un peu, c'est un patch rapidement mis en place car il est trop frustrant de voir ce genre de Move. Il y a une phase d'optimisation un peu plus fine dans le fichier optimisation.ml *)

let rec optimisation_code c = match c with
  |[] -> []
  |Ast4.Mov(a,b)::xs when a = b -> optimisation_code xs
  |x::xs -> x::(optimisation_code xs)
;;

let rec optimisation_fonction (f : Ast4.fonction) = 
  let filles = f.Ast4.filles in
  let nb = Array.length filles in
    for i = 0 to (nb-1) do
      filles.(i) <- optimisation_fonction filles.(i)
    done;
    {id = f.Ast4.id;
     nbRegistreVirtuel = f.Ast4.nbRegistreVirtuel;
     nbRegistreStatique = f.Ast4.nbRegistreStatique;
     nbEntParam = f.Ast4.nbEntParam;
     nbTablParam = f.Ast4.nbTablParam;
     tab = f.Ast4.tab;
     filles = f.Ast4.filles;
     corps = optimisation_code f.Ast4.corps;}
;;



let optimisation_programme (p : Ast4.programme) = 
  {tableauConsEnt = p.Ast4.tableauConsEnt; tableauString = p.Ast4.tableauString; principal = optimisation_fonction p.Ast4.principal; globale = p.Ast4.globale}
;;


(* Vivacité et allocation de registres et mini-optimisation , enfin*)
let vivacite (p : Ast3.programme) =
  let ht = creer_hashtbl p in
  let p2 = transforme_programme3_3bis p in
    optimisation_programme (transforme_programme_3bisto4 p2 ht)
;;
