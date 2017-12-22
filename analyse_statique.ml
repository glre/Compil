type fonction = { fonId : int list;
                  fonEnt : int; fonNbEntParam : int;
                  fonTab : int list; fonNbTabParam : int;
                  fonSous_proc : fonction option list;
                  fonCode : Ast2.code list}

type tipe =  Entier of Ast2.entier
            |Booleen of Ast2.booleen
            |RefEntier of Ast2.entier
            |RefBooleen of Ast2.entier
            |Tableau of Ast2.id * (int * int) list list * bool * Ast2.entier
            |String of int
            |NonSpecifie

exception Err2 of tipe*tipe
exception AnalyseStatique of string
exception InconsistenceDuParser of int
exception InconsistenceAnalyseStatique of int
exception ToDo of string
exception VariableLocalePourBoucle
type environnement = {entier : (string, Ast2.id*bool*bool) Hashtbl.t;(*nom, id, est_ce_booleen, est_ce_reference*)
                      mutable nb_entier : int;
                      constante : (string, int*bool) Hashtbl.t;(*nom, valeur, est_ce_booleen*)
                      tableau : (string, Ast2.id * (int * int) list list * bool) Hashtbl.t;
                            (*nom,id,dimensions,est_ce_booleen*)
                      mutable nb_tableau : int;
                      mutable dimension : int list;
                      valeur_tableau_constante : (int, (int * int) list list * int list * bool) Hashtbl.t;
                            (*no,dimensions,valeur,est_ce_booleen*)
                      tableau_constante : (string, int) Hashtbl.t;
                            (*nom, no dans la table de valeurs*)

                      mere : (int list) * (Ast.genre * bool) list * Ast.genre;
                      nom : string;
                    
                      fonctions_declarees_mere : (string, (int list) * (Ast.genre * bool) list * Ast.genre) Hashtbl.t;
                      fonctions_anticipees : (string, (int list) * (Ast.genre * bool) list * Ast.genre) Hashtbl.t;
                      fonctions : (string, (int list) * (Ast.genre * bool) list * Ast.genre) Hashtbl.t;

                            (*nom, id, (type, parValeur) list*)
                      mutable nb_fonction : int;
                      valeur_string_constante : (int, string) Hashtbl.t; (*nom, valeur*)
                      string_constante : (string, int) Hashtbl.t}

(*analyse*)
let analyse = fun ast ->
    (*duplique l'environnement*)
    let rec copie_env = fun env fo nom ->
        let retour = 
          {entier = Hashtbl.copy env.entier;
           nb_entier = 0;
           constante = Hashtbl.copy env.constante;
           tableau = Hashtbl.copy env.tableau;
           nb_tableau = 0;
           valeur_tableau_constante = env.valeur_tableau_constante;
           nb_fonction = 0;
           tableau_constante = Hashtbl.copy env.tableau_constante;
           nom = nom;
           mere = fo;
           
           fonctions = Hashtbl.create 1;
           fonctions_anticipees = Hashtbl.create 1;
           fonctions_declarees_mere = hash_union env.fonctions_anticipees env.fonctions_declarees_mere;

           dimension = [];
           valeur_string_constante = env.valeur_string_constante;
           string_constante = Hashtbl.copy env.string_constante;}
        in Hashtbl.add retour.fonctions_declarees_mere env.nom env.mere; retour;
    and hash_union = fun h1 h2 -> let r = Hashtbl.copy h1 in Hashtbl.iter (fun a b -> Hashtbl.add r a b) h2; r;
    and id_of_fo (a,b,c) = a
    and id_of_env env = id_of_fo (env.mere)
    and pr_of_env env = List.length (id_of_env env)
    and convertit_couple env = fun (p2,i2) -> match p2,i2 with (-1,i) -> (-1,i);|(p,i) -> ((pr_of_env env) - p),i
    (*copie un tableau dans un tableau*)
    and tat = fun env did sid indice indice2 taille -> let cc = convertit_couple env and ind = entier_frais env and ind2 = entier_frais env and tai = entier_frais env in
    	[(Ast2.Affectation_entier ((cc ind),indice));
         (Ast2.Affectation_entier ((cc ind2),indice2));
    	 (Ast2.Affectation_entier ((cc tai),taille));
    	 (Ast2.AppelProc([-1],[snd ind;snd ind2;snd tai],[cc did;cc sid]))]

    (*administratif*)
    and genre_of_tipe = fun g -> match g with
         Entier(e) -> Ast.Entier
        |Booleen(b) -> Ast.Booleen
        |Tableau(_,[],b,_) -> if b then Ast.Booleen else Ast.Entier
        |Tableau(id,(a::r),b,e) -> Ast.Tableau (a,(genre_of_tipe (Tableau(id,r,b,e))))
        |RefEntier(_) -> Ast.Ref (Ast.Entier)
        |RefBooleen(_) -> Ast.Ref (Ast.Booleen)
        |NonSpecifie -> raise (AnalyseStatique "une procedure ne peut etre utilisee comme une expression");
        |String _ -> raise (AnalyseStatique "pas de string en appel de fonction")
    (*administratif*)
    and taille_tableau env = fun nom -> 
        let rec taille_aux = fun t -> match t with
            [] -> 1
            |[[]] -> 1
            |[]::s -> taille_aux s
            |(((a,b)::r)::s) -> (b-a+1)*(taille_aux [r])*(taille_aux s)
        in
            let (_,d,_) = (Hashtbl.find env.tableau nom) in
            taille_aux d

    (*administratif*)
    and construit_type_tableau = fun type_ast -> match type_ast with (*trouve le type d'un tableau*)
        ([],_) -> raise (AnalyseStatique "TableauVide")
       |((a,b)::r,_) when a > b -> raise (AnalyseStatique "TableauDimensionNegative")
       |(l,Ast.Entier) -> [l],false
       |(l,Ast.Booleen)-> [l],true
       |(l,(Ast.Tableau (l',g'))) -> let dim,tipe = construit_type_tableau (l',g') in l::dim,tipe
       |_ -> raise (AnalyseStatique "TableauStringInterdit et tableaux de references")

    (*administratif*)
    and convertit_dimension_a_couple = fun t -> match t with
        [] -> []
        |0::r -> raise (AnalyseStatique "TableauVide")
        |a::r -> [0,a-1]::(convertit_dimension_a_couple r)

    (*administratif*)
    and convertit_couple_a_dimension = fun l -> match l with
                         [] -> []
                        |[[]] -> []
                        |[]::_ -> raise (InconsistenceAnalyseStatique 8)
                        |(((a,b)::r)::s) -> ((b-a+1)::(convertit_couple_a_dimension [r]))@(convertit_couple_a_dimension s)

    (*administratif*)
    and construit_type_tableau_constant env = fun co ->
        let dimension_constante env = fun s ->
            try
                let id = Hashtbl.find env.tableau_constante s in
                    try let d,v,b = Hashtbl.find env.valeur_tableau_constante id in
                                (if b then Ast.Booleen else Ast.Entier),(convertit_couple_a_dimension d),v
                    with Not_found -> raise (InconsistenceAnalyseStatique 9)
            with  Not_found -> raise (AnalyseStatique ("NomVariableAbsent: "^s))
        in
            match co with
              Ast.ConsInt i -> Ast.Entier,[],[i]
             |Ast.ConsBool b -> Ast.Booleen,[],[int_of_bool b]
             |Ast.ConsCons s -> begin try let v,b = Hashtbl.find env.constante s in if b then Ast.Booleen,[],[v] else Ast.Entier,[],[v]
                                    with Not_found -> dimension_constante env s end
             |Ast.ConsTableau [] -> raise (AnalyseStatique "TableauVide");
             |Ast.ConsTableau (a::r) -> let t,d,v'' = construit_type_tableau_constant env a in
                List.fold_left (fun res c -> match res with
                    (t,(a::r),v) ->
                        let t',d',v' = construit_type_tableau_constant env c in
                            if t != t' then raise (AnalyseStatique "TypeConstanteTableauIncompatible");
                            if r != d' then raise (AnalyseStatique "TypeTableauConstanteNonHomogene");
                            t,(a + 1)::r,v@v'
                    | _,[],_ -> raise (InconsistenceAnalyseStatique 7)
                               ) (t,1::d,v'') r
            |Ast.ConsString _ -> raise (AnalyseStatique "TableauStringInterdit")

            
    and int_of_bool b = if b then -1 else 0

    (*indique la presence de nom*)
    and est_present = fun env nom -> Hashtbl.mem env.entier nom
                                  || Hashtbl.mem env.constante nom
                                  || Hashtbl.mem env.tableau nom
                                  || Hashtbl.mem env.tableau_constante nom
                                  || Hashtbl.mem env.string_constante nom
                                  || Hashtbl.mem env.fonctions_declarees_mere nom
                                  || env.nom = nom
                                  || Hashtbl.mem env.fonctions_anticipees nom

    (*indique la presence parmi les variables*)
    and est_present_var = fun env nom -> Hashtbl.mem env.entier nom
                                  || Hashtbl.mem env.constante nom
                                  || Hashtbl.mem env.tableau nom
                                  || Hashtbl.mem env.tableau_constante nom
                                  || Hashtbl.mem env.string_constante nom


    (*donne un nouvel entier*)
    and entier_frais env = let retour = env.nb_entier in env.nb_entier <- retour +1; (pr_of_env env),retour
    and tableau_frais env = let retour = env.nb_tableau in env.nb_tableau <- retour +1; retour
    and fonction_fraiche env = let retour = env.nb_fonction in env.nb_fonction <- retour +1; retour
    and foo = fun a -> ()

    (*s'occupe des déclaration*)
    and construction_ast env = fun ast -> match ast with
 (*declaration d'une variable*)
       Ast.DecVar (nom,Ast.Booleen) when not (est_present env nom) || (not (est_present_var env nom) && nom = env.nom) ->
        Hashtbl.add env.entier nom ((entier_frais env),true,false);
        None

      |Ast.DecVar (nom,Ast.Entier) when not (est_present env nom) || (not (est_present_var env nom) && nom = env.nom) ->
        Hashtbl.add env.entier nom ((entier_frais env),false,false);
        None

      |Ast.DecVar (nom,Ast.Ref Ast.Booleen) when not (est_present env nom) || (not (est_present_var env nom) && nom = env.nom) ->
        Hashtbl.add env.entier nom ((entier_frais env),true,true);
        None

      |Ast.DecVar (nom,Ast.Ref Ast.Entier) when not (est_present env nom) || (not (est_present_var env nom) && nom = env.nom) ->
        Hashtbl.add env.entier nom ((entier_frais env),false,true);
        None

      |Ast.DecVar (nom,Ast.String)-> raise (AnalyseStatique "VariableStringNonConstante")

      |Ast.DecVar (nom,(Ast.Tableau (d,g))) when not (est_present env nom)  || (not (est_present_var env nom) && nom = env.nom) ->
        let dim,genre = construit_type_tableau (d,g)
        in Hashtbl.add env.tableau nom (((pr_of_env env), tableau_frais env), dim, genre);
           env.dimension <- (taille_tableau env nom)::env.dimension;
           None

      |Ast.DecVar (_,Ast.NonSpecifie) -> raise (InconsistenceDuParser 4)
      |Ast.DecVar (nom,_)  -> raise (AnalyseStatique ("NomDejaPresent1: "^ nom))

 (*declaration d'une constante*)
      |Ast.DecCons (nom,t,(Ast.ConsBool b)) when (t = Ast.Booleen || t = Ast.NonSpecifie) && not (est_present env nom) ->
        Hashtbl.add env.constante nom (int_of_bool b,true); None

      |Ast.DecCons (nom,t,(Ast.ConsInt i)) when (t = Ast.Entier || t = Ast.NonSpecifie) && not (est_present env nom) ->
        Hashtbl.add env.constante nom (i,false); None

      |Ast.DecCons (nom,t,(Ast.ConsString s)) when (t = Ast.String || t = Ast.NonSpecifie) && not (est_present env nom) ->
        let id = Hashtbl.length env.valeur_string_constante
        in
            Hashtbl.add env.string_constante nom id;
            Hashtbl.add env.valeur_string_constante id s; None

      |Ast.DecCons (nom,Ast.Tableau (dim,ti),(Ast.ConsTableau l as c)) when not (est_present env nom) ->
            let t,d,v = construit_type_tableau_constant env c
            and d',b = construit_type_tableau (dim,ti) in
            if (convertit_couple_a_dimension d') = d then
                if b = (t = Ast.Booleen) then
                    let id = Hashtbl.length env.valeur_tableau_constante in                        
                        Hashtbl.add env.valeur_tableau_constante id (d',List.rev v,b);
                        Hashtbl.add env.tableau_constante nom id; None
                else raise (AnalyseStatique "TypeConstanteErrone")
            else raise (AnalyseStatique "DimensionsIncompatibles")

      |Ast.DecCons (nom,Ast.NonSpecifie,(Ast.ConsTableau l as c)) when not (est_present env nom) ->
            let t,d,v = construit_type_tableau_constant env c
            and id = Hashtbl.length env.valeur_tableau_constante
            in 
                Hashtbl.add env.valeur_tableau_constante id ((convertit_dimension_a_couple d),List.rev v,(t = Ast.Booleen));
                Hashtbl.add env.tableau_constante nom id; None
        
      |Ast.DecCons (nom,t,(Ast.ConsCons nom2)) when not (est_present env nom) -> begin try let i = Hashtbl.find env.constante nom2 in Hashtbl.add env.constante nom i with Not_found -> try let t = Hashtbl.find env.tableau_constante nom2 in Hashtbl.add env.tableau_constante nom2 t with Not_found -> raise (AnalyseStatique ("NomVariableAbsent: "^ nom2)) end; None

      |Ast.DecCons (nom,_,_) -> raise (AnalyseStatique ("NomDejaPresent2: " ^ nom))
    
     (*declaration anticipée d'une procedure*)
      |Ast.DecFonc (nom,param2,genre,sous_proc,(Ast.Vide)) when not (est_present env nom) ->
         let id = fonction_fraiche env
         in
            Hashtbl.add env.fonctions_anticipees nom
            (
              (id::(id_of_env env)),
              (List.map (
                 fun t -> match t with
                     Ast.ParValeur(_,g) -> (g,true)
                    |Ast.ParAdresse(_,g) -> (g,false)) param2),
               genre
            );
            None;

      (*déclaration du corps de la fonction*)
      |Ast.DecFonc (nom,param2,genre,sous_proc,(Ast.BeginEnd(_) as code)) when (Hashtbl.mem env.fonctions_anticipees nom) ->
            (*ajoute le retour en paramètre*)
            let param = match genre with Ast.NonSpecifie -> param2 | _ as g -> Ast.ParAdresse(nom,g)::param2 in    
              let id,tipe,retour = Hashtbl.find env.fonctions_anticipees nom in
                if (retour <> genre) || ((List.map (
                   fun t -> match t with
                       Ast.ParValeur(_,g) -> (g,true)
                      |Ast.ParAdresse(_,g) -> (g,false)) param2) <> tipe || retour <> genre)
                then
                  raise (AnalyseStatique ("Type incompatible avec déclaration anticipée"));
                
              (*déclare la fonction comme ayant un corps*)
                Hashtbl.add env.fonctions nom
                (
                  id,
                  tipe,
                  retour
                );

                let new_env = copie_env env (id,tipe,retour) nom in
                  let nb_ancien_entier = new_env.nb_entier
                  and nb_ancien_tableau = new_env.nb_tableau
                  and cc = convertit_couple new_env in
                    (*declare les paramètres*)
                    List.iter (fun p -> match p with
                        Ast.ParValeur(nom,genre) -> foo(construction_ast new_env (Ast.DecVar (nom,genre)))
                       |Ast.ParAdresse(nom,genre) -> foo(construction_ast new_env (Ast.DecVar (nom,genre)))
                              ) param;
                    let nb_entier = new_env.nb_entier - nb_ancien_entier
                    and nb_tableau = new_env.nb_tableau - nb_ancien_tableau in
                      let new_sous_proc = List.map (construction_ast new_env) sous_proc in
                         (*copie les variables passées par valeur*)
                         let debut_code = List.fold_right
                           (fun p code_tmp -> match p with
                               Ast.ParValeur(nom,g) when g=Ast.Booleen || g=Ast.Entier || g=Ast.Ref Ast.Entier || g=Ast.Ref Ast.Booleen->
                                 let old_id,_,_ = (Hashtbl.find new_env.entier nom) in
                                   Hashtbl.remove new_env.entier nom;
                                   foo(construction_ast new_env (Ast.DecVar (nom,g)));
                                   let id2,_,_ = Hashtbl.find new_env.entier nom in
                                     (match g with
                                        Ast.Entier -> (Ast2.Affectation_entier ((cc id2),(Ast2.Variable_entier (cc old_id))))::code_tmp
                                       |Ast.Ref Ast.Entier -> (Ast2.Affectation_entier ((cc id2),(Ast2.Variable_entier (cc old_id))))::code_tmp
                                       |Ast.Ref Ast.Booleen -> (Ast2.Affectation_entier ((cc id2),(Ast2.Variable_entier (cc old_id))))::code_tmp
                                       |Ast.Booleen -> (Ast2.Affectation_booleen (cc id2,(Ast2.Variable_booleen (cc old_id))))::code_tmp
                                       |_ -> raise (InconsistenceAnalyseStatique 42))
                              |Ast.ParValeur(nom,(Ast.Tableau(_,_) as g)) ->
                                 let old_id,_,_ = Hashtbl.find new_env.tableau nom in
                                   Hashtbl.remove new_env.tableau nom;
                                   foo(construction_ast new_env (Ast.DecVar (nom,g)));
                                   let id2,_,_ = Hashtbl.find new_env.tableau nom in
                                     (tat new_env id2 old_id
                                       (Ast2.Const_entier 0)
                                       (Ast2.Const_entier 0)
                                       (Ast2.Const_entier(taille_tableau new_env nom)))@code_tmp
                              |Ast.ParAdresse (a,b) -> code_tmp
                              |_ ->raise (InconsistenceAnalyseStatique 6)
                           )
                           param
                           []
                         in
                           let code_final,dedp = transforme_code new_env debut_code code in
                             Some({fonId = id_of_env new_env;
                                   fonEnt = new_env.nb_entier;
                                   fonNbEntParam = nb_entier;
                                   fonTab = new_env.dimension;
                                   fonNbTabParam = nb_tableau;
                                   fonSous_proc = new_sous_proc;
                                   fonCode = code_final})

      (*déclaré une fonction, c'est déclarer son prototype puis son corps*)
      |Ast.DecFonc (nom,param,genre,sous_proc,(Ast.BeginEnd(_) as code)) when not (est_present env nom) ->
         foo(construction_ast env (Ast.DecFonc (nom,param,genre,sous_proc,Ast.Vide)));
         construction_ast env (Ast.DecFonc (nom,param,genre,sous_proc,code));
        
      |Ast.DecFonc (nom,_,_,_,_) -> raise (AnalyseStatique ("NomDejaPresent4: "^ nom))
    and
        transforme_code = fun env debut_code code ->
            let cc = convertit_couple env in
           (*renvoie le type ainsi que la valeur, le code préambule, et les variables utilisées (plus à jour et inutilisé)*)
            let rec compile_expr = fun expr -> 
            match expr with
                 Ast.Rftoint (a) -> let ca,sa,va = compile_expr a in (
                   match ca with
                      RefEntier (entier)-> Entier(entier),sa,[]
                     |_ -> raise (AnalyseStatique ("^ ne doit etre utilise que avec des ref int"));
                      )

                |Ast.Inttorf (a) -> let ca,sa,va = compile_expr a in (
                   match ca with
                      Entier (entier)-> RefEntier(entier),sa,[]
                     |_ -> raise (AnalyseStatique ("@ ne doit etre utilise que avec des int"));
                      )
  
                |Ast.Read -> Entier(Ast2.Read),[],[]
                |Ast.Dereference (a) -> let ca,sa,va = compile_expr a in (
                   match ca with
                      RefEntier (entier)-> Entier(Ast2.Dereference_entier (entier)),sa,[]
                     |RefBooleen (entier)-> Booleen(Ast2.Dereference_booleen (entier)),sa,[]
                     |_ -> raise (AnalyseStatique ("dereferencement de reference seulement")))
                |Ast.Adresse (a) -> let ca,sa,va = compile_expr a in (
                   match ca with
                       Tableau (id,[[_]],false,offset) -> RefEntier(Ast2.Adresse(cc id,offset)),sa,[]
                      |Tableau (id,[[_]],true,offset) -> RefBooleen(Ast2.Adresse(cc id,offset)),sa,[]
                      |_ -> raise (AnalyseStatique ("seuls les tableaux unidimensionnels peuvent etre references")))


                |Ast.ConsExpr (Ast.ConsInt i) -> Entier(Ast2.Const_entier i),[],[]
                |Ast.ConsExpr (Ast.ConsBool b) -> Booleen(Ast2.Const_booleen b),[],[]
                |Ast.ConsExpr (Ast.ConsString s) -> let id = Hashtbl.length env.valeur_string_constante in
                                                        Hashtbl.add env.valeur_string_constante id s;
                                                        String(id),[],[]
                |Ast.ConsExpr (Ast.ConsTableau _) -> raise (InconsistenceDuParser 1)
                |Ast.ConsExpr (Ast.ConsCons _) -> raise (InconsistenceDuParser 2)
                |Ast.Plus (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Entier(Ast2.Plus (ta,tb)),(sa@sb),(va@vb)
                        |(RefEntier(ta),Entier(tb)) -> RefEntier(Ast2.Plus (ta,Ast2.Fois(tb,Ast2.Const_entier 4))), (sa@sb),(va@vb)
                        |(RefBooleen(ta),Entier(tb)) -> RefBooleen(Ast2.Plus (ta,Ast2.Fois(tb,Ast2.Const_entier 4))), (sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Fois(a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Entier(Ast2.Fois (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Moins (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Entier(Ast2.Moins (ta,tb)),(sa@sb),(va@vb)
                        |(RefEntier(ta),RefEntier(tb)) -> RefEntier(Ast2.Div ((Ast2.Moins (ta,tb)),Ast2.Const_entier 4)), (sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Dividende (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Entier(Ast2.Div (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Modulo (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Entier(Ast2.Modulo (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Supeq (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Booleen(Ast2.Supeq (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Sup (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Booleen(Ast2.Sup (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Infeq (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Booleen(Ast2.Infeq (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Inf (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Entier(ta),Entier(tb)) -> Booleen(Ast2.Inf (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "EntierAttendu"))
                |Ast.Et (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Booleen(ta),Booleen(tb)) -> Booleen(Ast2.Et (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "BooleenAttendu"))
                |Ast.Ou (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Booleen(ta),Booleen(tb)) -> Booleen(Ast2.Ou (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "BooleenAttendu"))

                |Ast.New a -> let ca,sa,va = compile_expr a in
                    (match ca with
                         Entier(ta) ->
                             let id_tmp = entier_frais env and id_tmp2 = entier_frais env
                             in
                               RefEntier(Ast2.Variable_entier (convertit_couple env id_tmp)),
                                sa@[Ast2.Affectation_entier (cc id_tmp2,Ast2.Fois(ta,Ast2.Const_entier 4));Ast2.AppelProc ([-10],[snd id_tmp; snd id_tmp2],[])],va
                        |_ -> raise (AnalyseStatique "New entier"))

                |Ast.Non a -> let ca,sa,va = compile_expr a in
                    (match ca with
                         Booleen(ta) -> Booleen(Ast2.Non ta),sa,va
                        |_ -> raise (AnalyseStatique "BooleenAttendu"))
                |Ast.Eq (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Booleen(ta),Booleen(tb)) -> Booleen(Ast2.EqBool (ta,tb)),(sa@sb),(va@vb)
                        |(Entier(ta),Entier(tb)) -> Booleen(Ast2.Eq (ta,tb)),(sa@sb),(va@vb)
                        |(RefEntier(ta),RefEntier(tb)) -> Booleen(Ast2.Eq (ta,tb)),(sa@sb),(va@vb)
                        |(RefBooleen(ta),RefBooleen(tb)) -> Booleen(Ast2.Eq (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "DeuxTypesIdentiquesAttendus"))
                |Ast.Neq (a,b) -> let ca,sa,va = compile_expr a and cb,sb,vb = compile_expr b in
                    (match (ca,cb) with
                         (Booleen(ta),Booleen(tb)) -> Booleen(Ast2.NeqBool (ta,tb)),(sa@sb),(va@vb)
                        |(Entier(ta),Entier(tb)) -> Booleen(Ast2.Neq (ta,tb)),(sa@sb),(va@vb)
                        |(RefEntier(ta),RefEntier(tb)) -> Booleen(Ast2.Neq (ta,tb)),(sa@sb),(va@vb)
                        |(RefBooleen(ta),RefBooleen(tb)) -> Booleen(Ast2.Neq (ta,tb)),(sa@sb),(va@vb)
                        |_ -> raise (AnalyseStatique "DeuxTypesIdentiquesAttendus"))

                |Ast.AppelFonc(nom,param) ->
                    begin
                      let id,tparam,retour =
                        try Hashtbl.find env.fonctions_anticipees nom
                        with Not_found -> 
                          try Hashtbl.find env.fonctions_declarees_mere nom
                          with Not_found ->
                            if nom = env.nom then
                               env.mere
                            else
                               raise (AnalyseStatique ("Fonction_inconnue :"^nom))
                      in
                      (*entiers à passer en paramètre, tableaux à passer, code préambule, truc inutile*)
                      let ent,tab,c,v = List.fold_right2
                        (
                          fun expr t (entr,tabr,cr,vr) ->
                            let p,c,v = compile_expr expr in 
                              if (genre_of_tipe p <> fst t) then
                                raise (AnalyseStatique "Parametres passés à fonction incompatibles");
                              match p,t with
                                 Entier(e),(_,true) ->
                                   let id = entier_frais env
                                   in
                                     (snd id)::entr,
                                     tabr,
                                     c@cr@[Ast2.Affectation_entier ((cc id),e)],
                                     v@vr
                                |Entier(Ast2.Variable_entier (0,i)),(_,false) ->
                                   i::entr,tabr,c@cr,
                                   v@vr
                                |RefEntier(e),(_,true) ->
                                   let id = entier_frais env
                                   in
                                     (snd id)::entr,
                                     tabr,
                                     c@cr@[Ast2.Affectation_entier ((cc id),e)],
                                     v@vr
                                |RefEntier(Ast2.Variable_entier (0,i)),(_,false) ->
                                   i::entr,tabr,c@cr,
                                   v@vr
                                |RefBooleen(e),(_,true) ->
                                   let id = entier_frais env
                                   in
                                     (snd id)::entr,
                                     tabr,
                                     c@cr@[Ast2.Affectation_entier ((cc id),e)],
                                     v@vr
                                |RefBooleen(Ast2.Variable_entier (0,i)),(_,false) ->
                                   i::entr,tabr,c@cr,
                                   v@vr
                                |Booleen(e),(_,true) ->
                                   let id = entier_frais env
                                   in
                                     (snd id)::entr,
                                     tabr,
                                     c@cr@[Ast2.Affectation_booleen ((cc id),e)],
                                     v@vr
                                |Booleen(Ast2.Variable_booleen (0,i)),(_,false) ->
                                   i::entr,tabr,c@cr,
                                   v@vr
                                |Tableau(i,d,b,indice),(_,true) ->
                                   let id = tableau_frais env and taille = taille_tableau d
                                   in
                                     env.dimension <- taille::env.dimension;
                                     entr,
                                     (0,id)::tabr,
                                     c@cr@(tat env ((pr_of_env env),id) i (Ast2.Const_entier 0) indice (Ast2.Const_entier taille)),
                                     v@vr
                                |Tableau(i,d,b,indice),(_,false) when indice = (Ast2.Const_entier 0) ->
                                   entr,
                                   (cc i)::tabr,
                                   c@cr,
                                   v@vr
                                |_ -> raise (AnalyseStatique "ne passez ni d'expressions, ni de variables de mères par references!")
                        )
                        param
                        tparam
                        ([],[],[],[])
                      in
                        match retour with
                          (*traite la variable de retour*)
                           Ast.Entier ->
                             let id_tmp = entier_frais env
                             in
                               Entier(Ast2.Variable_entier (convertit_couple env id_tmp)),c@[Ast2.AppelProc (id,(snd id_tmp)::ent,tab)],v
                          |Ast.Booleen ->
                             let id_tmp = entier_frais env
                             in
                                Booleen(Ast2.Variable_booleen (convertit_couple env id_tmp)),c@[Ast2.AppelProc(id,(snd id_tmp)::ent,tab)],v
                          |Ast.Tableau(d,g) ->
                             let dim,genre = construit_type_tableau (d,g)
                             in
                               let id_tmp = tableau_frais env
                               in env.dimension <- (taille_tableau dim)::env.dimension;
                                  Tableau((pr_of_env env,id_tmp), dim, genre, Ast2.Const_entier 0),c@[Ast2.AppelProc(id,ent,((0,id_tmp)::tab))],v
                          |Ast.NonSpecifie -> NonSpecifie,c@[Ast2.AppelProc(id,ent,tab)],v
                          |Ast.Ref Ast.Entier ->
                             let id_tmp = entier_frais env
                             in
                               RefEntier(Ast2.Variable_entier (convertit_couple env id_tmp)),c@[Ast2.AppelProc (id,(snd id_tmp)::ent,tab)],v
                          |Ast.Ref Ast.Booleen ->
                             let id_tmp = entier_frais env
                             in
                               RefEntier(Ast2.Variable_entier (convertit_couple env id_tmp)),c@[Ast2.AppelProc (id,(snd id_tmp)::ent,tab)],v
                          |_ -> raise (InconsistenceAnalyseStatique 3)
                    end;

                (*accès à une variable*)
                |Ast.AccesTabl(nom,[]) -> begin
					         try
                     let ((p,i),b,r) = Hashtbl.find env.entier nom
                     in
	                      (match b,r with  true,false -> Booleen(Ast2.Variable_booleen (cc (p,i)))
                                        |false,false -> Entier(Ast2.Variable_entier (cc (p,i)))
                                        |true,true -> RefBooleen(Ast2.Variable_entier (cc (p,i)))
                                        |false,true -> RefEntier(Ast2.Variable_entier (cc (p,i)))
       	                ),[],
      	                (if p<(pr_of_env env) then [(p,i)]
    	                                        else []
    	                  )
					          with Not_found ->
                    try
                      let v,b = Hashtbl.find env.constante nom
                      in
						            (if b then Booleen(Ast2.Const_booleen (v = -1))
                              else (Entier(Ast2.Const_entier v))),[],[]
					          with Not_found ->
					          try
                      let id,dim,b = Hashtbl.find env.tableau nom
                      in
            						(Tableau(id,dim,b,(Ast2.Const_entier 0))),[],[]
          					with Not_found ->
					          try
                      let id = Hashtbl.find env.tableau_constante nom
                      in
  					          	let dim,_,b = Hashtbl.find env.valeur_tableau_constante id
                        in
		    				          (Tableau((-1, id),dim,b,(Ast2.Const_entier 0))),[],[]
										with Not_found ->
						          raise (AnalyseStatique ("NomAbsent: "^nom)) end

                (*accès à un tableau*)
                |Ast.AccesTabl(nom,a) -> let (id,dim,b) = (try Hashtbl.find env.tableau nom
                                                  with Not_found -> try let i = Hashtbl.find env.tableau_constante nom in
                                                                   let d,_,b = Hashtbl.find env.valeur_tableau_constante i in ((convertit_couple env (-1,i)),d,b)
                                                                    with Not_found -> raise (AnalyseStatique ("NomAbsent: "^nom)))
                                        in

                                        let eg = (fun e1 e2 -> (List.map (fun _ -> ()) e1) = (List.map (fun _ -> ()) e2)) in
                                        let suff = suffixe a dim eg (*suff type tableau restant*)
                                        in
                                            if suff = [] then
                                                compile_tableau_vers_entier (id,dim,b) a
                                            else
                                                compile_tableau_vers_tableau env (id,dim,b) a suff eg



    and taille_tableau = fun l ->
      match l with
         [] -> 1
        |[[]] -> 1
        |(((a,b)::r)::s) -> (b-a+1)*(taille_tableau [r])*(taille_tableau s)
        |([]::r) -> taille_tableau r
    and compile_tableau_vers_tableau env = fun (id,dim,b) a nouveau_dim eg ->
      let i',p' = id in
      let valeur_utilise = if p' < (pr_of_env env) then [id] else [] in

      let decalage = (taille_tableau nouveau_dim)
      and i = tableau_frais env in
          env.dimension <- (List.fold_left (fun a b -> a*b) 1 (List.map (fun (a,b) -> b-a+1) (List.flatten nouveau_dim)))::env.dimension; 
          let dim_deroule = List.flatten (prefixe a dim eg)
          and a_deroule = List.flatten a in
              let _,ind,code,valeur = List.fold_right2 (

                  fun indice (inf,sup) (produit,e,s,v) -> match compile_expr indice with
                      Entier(e'),sa,va ->
                          produit / (sup - inf + 1),
                          Ast2.Plus(Ast2.Fois(Ast2.Moins(e',Ast2.Const_entier(inf)),Ast2.Const_entier(produit*4)),e),
                          (s@sa),
                          (v@va)
                      |_ -> raise (AnalyseStatique "EntierAttendu")
                                                       )
                                                       a_deroule
                                                       dim_deroule
                                                       ((List.fold_left (fun t (i,s) -> t*(s-i+1)) 1 (List.flatten nouveau_dim)),Ast2.Const_entier(0),[],[])
                       in Tableau(id,nouveau_dim,b,(Ast2.Fois (ind,Ast2.Const_entier decalage))),
                          (tat env (i,(pr_of_env env)) id (Ast2.Const_entier 0) ind (Ast2.Const_entier decalage))@code,
                          valeur_utilise@valeur
                
     and compile_tableau_vers_entier = fun (id,dim,b) a ->
          let i,p = id in
          let valeur_utilise = if p < (pr_of_env env) then [id] else [] in
          let dim_deroule = List.fold_left (fun suite dim_locale -> suite@dim_locale) [] dim
          and a_deroule = List.fold_left (fun suite a_locale -> suite@a_locale) [] a in
              let _,ind,code,valeur = List.fold_right2 (fun indice (inf,sup) (produit,e,s,v) -> match compile_expr indice with
                  Entier(e'),sa,va ->
                      produit * (sup - inf + 1),
                      Ast2.Plus(Ast2.Fois(Ast2.Moins(e',Ast2.Const_entier(inf)),Ast2.Const_entier(produit*4)),e),
                      (s@sa),
                      (v@va)
                  |_ -> raise (AnalyseStatique "EntierAttendu"))
                                                       a_deroule
                                                       dim_deroule
                                                       (1,Ast2.Const_entier(0),[],[])
                       in if b then Booleen(Ast2.Acces_tableau_booleen(cc id,ind)),code,valeur@valeur_utilise
                               else Entier(Ast2.Acces_tableau_entier(cc id,ind)),code,valeur@valeur_utilise

     and suffixe = fun l m eg -> match (l,m) with                        
         ([],m) -> m
         |((a::r),(b::s)) when (eg a b) -> suffixe r s eg
         |((a::r),(b::s)) -> raise (AnalyseStatique "TableauxIncompatibles")
         |((a::r),[]) -> raise (AnalyseStatique "TableauxIncompatibles")


     and prefixe = fun l m eg -> match (l,m) with                        
         ([],m) -> []
         |((a::r),(b::s)) when (eg a b) -> b::(prefixe r s eg)
         |((a::r),(b::s)) -> raise (AnalyseStatique "TableauxIncompatibles")
         |((a::r),[]) -> raise (AnalyseStatique "TableauxIncompatibles")

     and compile_code_aux = fun code -> match code with
           Ast.BeginEnd(l) -> List.fold_left (fun (ctr,vtr) c -> let ct,vt = (compile_code_aux c) in (ctr@ct),(vtr@vt)) ([],[]) l
             (*affectation*)
          |Ast.Affectation (k,va) -> let sti,sco,_ = compile_expr va in
            begin match k with
              Ast.Dereference(rf) -> let dti,dco,_ = compile_expr rf in
                begin
                  match dti,sti with
                     RefEntier(e),Entier(f) -> sco@dco@[Ast2.Affectation_ref_entier (e,f)],[]
                    |RefBooleen(e),Booleen(f) -> dco@sco@[Ast2.Affectation_ref_booleen (e,f)],[]
                    |_ -> raise (AnalyseStatique "incompatibilite types")
                end

             |Ast.AccesTabl(nom,e10) ->
              begin
                match e10 with
                  [] -> (*let e,s,c = compile_expr va in*)
                    begin
                      match sti with
                       |Entier(en) -> (try let (i,p),b,r = Hashtbl.find env.entier nom in if b = true || r = true then raise Not_found;
                               sco@[Ast2.Affectation_entier (cc (i,p),en)],[]
                                      with Not_found -> raise (AnalyseStatique ("EntierIntrouvable: " ^ nom)))
                       |Booleen(en) -> (try let (i,p),b,r = Hashtbl.find env.entier nom in if b = false || r = true then raise Not_found;
                               sco@[Ast2.Affectation_booleen (cc (i,p),en)],[]
                                      with Not_found -> raise (AnalyseStatique ("BooleenIntrouvable: " ^ nom)))
                       |RefEntier(en) -> (try let (i,p),b,r = Hashtbl.find env.entier nom in if b = true || r = false then raise Not_found;
                               sco@[Ast2.Affectation_entier (cc (i,p),en)],[]
                                      with Not_found -> raise (AnalyseStatique ("RefEntierIntrouvable: " ^ nom)))
                       |RefBooleen(en) -> (try let (i,p),b,r = Hashtbl.find env.entier nom in if b = false || r = false then raise Not_found;
                               sco@[Ast2.Affectation_entier (cc (i,p),en)],[]
                                      with Not_found -> raise (AnalyseStatique ("RefBooleenIntrouvable: " ^ nom)))

                       |Tableau(id,dim,b,en) -> (try let (p,i),d,b' = Hashtbl.find env.tableau nom in if b <> b' then raise Not_found; if d <> dim then raise (AnalyseStatique "DimensionsIncompatibles");
                               sco@(tat env (p,i) id (Ast2.Const_entier 0) en (Ast2.Const_entier (taille_tableau dim))),[]
                                      with Not_found -> raise (AnalyseStatique ("EntierIntrouvable: " ^ nom)))
                       |NonSpecifie -> raise (AnalyseStatique "une procedure ne peut etre utilisee comme une expression");
                       |_ -> raise (AnalyseStatique "Pas d'affectation de string ou de references");
                      end
                  |_ -> let dti,dco,_ = compile_expr (Ast.AccesTabl (nom,e10)) in
                    begin
                      match dti,sti with
                          Entier(Ast2.Acces_tableau_entier(id,ind)),Entier(en) -> dco@sco@[Ast2.Affectation_tae (id,ind,en)],[]
                         |Booleen(Ast2.Acces_tableau_booleen(id,ind)),Booleen(en) -> dco@sco@[Ast2.Affectation_tab (id,ind,en)],[]
                         |Tableau(id,dim,b,ind),Tableau(id2,dim2,b2,ind2) when (fst id <> -1) && dim2=dim && b = b2 -> dco@sco@(tat env id id2 ind ind2 (Ast2.Const_entier (List.fold_left (fun a b -> a*b) 1 (List.map (fun (a,b) -> b-a+1) (List.flatten dim)) ))),[]
                         |_ -> raise (AnalyseStatique "incompatibilite dimensions tableaux ou affectation de constante")
                     end;
              end
              |_->raise (AnalyseStatique "affectation impossible");
            end


         |Ast.Exit ->  [Ast2.Exit],[]

         |Ast.Ifte(b,e1,e2) -> begin let e,c,v = compile_expr b in match e with
             Booleen(b') ->
                 let th,vth = compile_code_aux e1 and el,vel = compile_code_aux e2 in
                     c@[Ast2.Ifte (b',th,el)],(v@vth@vel)
             |_ -> raise (AnalyseStatique "booleen attendu dans if then else") end
         |Ast.TantQue(b,e1) ->   begin let e,c,v = compile_expr b in match e with
             Booleen(b') ->
                 let th,vth = compile_code_aux e1 in
                     [Ast2.TantQue (b',c,th)],(v@vth)
             |_ -> raise (AnalyseStatique "booleen attendu dans while") end
         |Ast.FaitJusquA (e1,b) -> begin let e,c,v = compile_expr b in match e with
             Booleen(b') ->
                 let th,vth = compile_code_aux e1 in
                     [Ast2.FaitJusquA (th@c,b')],(v@vth)
             |_ -> raise (AnalyseStatique "booleen attendu dans while") end

          |Ast.Free a -> let ca,sa,va = compile_expr a in
              (match ca with
                   RefEntier(ta) ->
                       let id_tmp2 = entier_frais env
                       in
                          sa@[Ast2.Affectation_entier (cc id_tmp2,ta);Ast2.AppelProc ([-11],[snd id_tmp2],[])],va
                  |_ -> raise (AnalyseStatique "New entier"))

         |Ast.Boucle(s,deb,fin,incr,corps) -> begin try
            let (p,id),b,r = Hashtbl.find env.entier s in
              if p <> (pr_of_env env) then raise VariableLocalePourBoucle; if b = true || r = true then raise Not_found;  
                 let d,sd,vd = compile_expr deb and f,sf,vf = compile_expr fin and c,vc = compile_code_aux corps in match (d,f) with
                     (Entier(b1),Entier(b2)) -> sd@sf@[Ast2.Boucle (id,b1,b2,incr,c)],vd@vc@vf
                     |_,_ -> raise (AnalyseStatique "EntierAttenduDansBoucle") with Not_found -> raise (AnalyseStatique ("VariableEntierAttenduDansBoucle: "^s)) end

        (*infere le type de write*)
         |Ast.Write(param) ->
            let p,c,v = compile_expr param
            in
              begin
                match p with
                   Entier(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WriteInt(snd id)],
                       []
                  |Booleen(b) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_booleen ((convertit_couple env id),b);Ast2.AppelProc ([-4],[snd id],[])],
                       []

                  |RefEntier(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WriteInt(snd id)],
                       []


                  |RefBooleen(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WriteInt(snd id)],
                       []


                  |Tableau(id,dim,true,ind) ->
                     let ide = entier_frais env and ide2 = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((cc ide),ind);
                          Ast2.Affectation_entier ((cc ide2),Ast2.Const_entier (List.fold_left (fun a (b,c) -> a*(c-b+1)) 1 (List.flatten dim)));
                          Ast2.AppelProc ([-6], [snd ide; snd ide2], [cc id])],
                       []
                  |Tableau(id,dim,false,ind) ->
                     let ide = entier_frais env and ide2 = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((cc ide),ind);
                          Ast2.Affectation_entier ((cc ide2),Ast2.Const_entier(List.fold_left (fun a (b,c) -> a*(c-b+1)) 1 (List.flatten dim)));
                          Ast2.AppelProc ([-2], [snd ide; snd ide2], [cc id])],
                       []
                  |String(i) -> [Ast2.WriteString i],[]
                  |NonSpecifie -> raise (AnalyseStatique "une procedure ne peut etre utilisee comme une expression");
              end;


         |Ast.Writeln(param) ->
            let p,c,v = compile_expr param
            in
              begin
                match p with
                   Entier(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WritelnInt(snd id)],
                       []
                  |Booleen(b) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_booleen ((convertit_couple env id),b);Ast2.AppelProc ([-5],[snd id],[])],
                       []

                  |RefEntier(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WritelnInt(snd id)],
                       []


                  |RefBooleen(e) ->
                     let id = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((convertit_couple env id),e);Ast2.WritelnInt(snd id)],
                       []

                  |Tableau(id,dim,true,ind) ->
                     let ide = entier_frais env and ide2 = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((cc ide),ind);
                          Ast2.Affectation_entier ((cc ide2),Ast2.Const_entier (List.fold_left (fun a (b,c) -> a*(c-b+1)) 1 (List.flatten dim)));
                          Ast2.AppelProc ([-7], [snd ide; snd ide2], [cc id])],
                       []
                  |Tableau(id,dim,false,ind) ->
                     let ide = entier_frais env and ide2 = entier_frais env
                     in
                       c@[Ast2.Affectation_entier ((cc ide),ind);
                          Ast2.Affectation_entier ((cc ide2),Ast2.Const_entier(List.fold_left (fun a (b,c) -> a*(c-b+1)) 1 (List.flatten dim)));
                          Ast2.AppelProc ([-3], [snd ide; snd ide2], [cc id])],
                       []
                  |String(i) -> [Ast2.WritelnString i],[]
                  |NonSpecifie -> raise (AnalyseStatique "une procedure ne peut etre utilisee comme une expression");
              end;

         |Ast.AppelProc(nom,param) ->
            let _,c,v = compile_expr (Ast.AppelFonc(nom,param))
            in
              c,v
         |Ast.Vide -> [],[]
             
        in
             let c,v = compile_code_aux code in
             (debut_code @  c),v

                        

in
  match ast with
     Ast.DecFonc (s, _,Ast.Entier,liste_declaration, _) ->
       let env =
         {
           entier = Hashtbl.create 1;
           constante = Hashtbl.create 1;
           tableau  = Hashtbl.create 1;
           valeur_tableau_constante = Hashtbl.create 1;
           tableau_constante = Hashtbl.create 1;

           fonctions_anticipees = Hashtbl.create 1;
           fonctions_declarees_mere = Hashtbl.create 1;
           fonctions = Hashtbl.create 1;

           nom = "1racine";
           mere = [],[],Ast.NonSpecifie;           

           string_constante  = Hashtbl.create 1;
           nb_entier = 0; nb_fonction = 0;
           nb_tableau = 0;
           valeur_string_constante = Hashtbl.create 1;
           dimension = []
         }
       in
         Hashtbl.add env.valeur_string_constante 0 "true";
         Hashtbl.add env.string_constante "0true" 0;
         Hashtbl.add env.valeur_string_constante 1 "false";
         Hashtbl.add env.string_constante "1false" 1;
         Hashtbl.add env.valeur_string_constante 2 "[|";
         Hashtbl.add env.string_constante "2[|" 2;
         Hashtbl.add env.valeur_string_constante 3 "|]";
         Hashtbl.add env.string_constante "3|]" 3;
         Hashtbl.add env.valeur_string_constante 4 ";";
         Hashtbl.add env.string_constante "4;" 4;
         Hashtbl.add env.valeur_string_constante 5 "\\n";
         Hashtbl.add env.string_constante "5n" 5;
         Hashtbl.add env.valeur_string_constante 6 "enregistrement:";
         Hashtbl.add env.string_constante "6e" 6;

         let r = (construction_ast env ast)
         in
           (r,env.valeur_tableau_constante,env.valeur_string_constante)
    |_ -> raise (InconsistenceDuParser 3);;

let analyse_statique = fun ast ->

    let rec aux = fun fon -> match fon with
      { fonId = id;
            fonEnt = ent; fonNbEntParam = nbentparam; 
            fonTab = tab; fonNbTabParam = nbtabparam;
            fonSous_proc = fonssprc;
            fonCode = code} ->
   {Ast2.fonId=id;
    Ast2.fonEnt = ent; Ast2.fonNbEntParam = nbentparam;
    Ast2.fonTab = Array.of_list tab; Ast2.fonNbTabParam = nbtabparam;
    Ast2.fonSous_proc = Array.of_list (List.fold_right (fun f r -> match f with None -> r
                                                                               |(Some f') -> (aux f')::r) fonssprc []);
    Ast2.fonCode = code}
    
    and aux2 = fun htbl ->
        let retour = Array.make (Hashtbl.length htbl) (Array.make 1 0)
        in
            for i = 0 to (Array.length retour)-1 do
                let _,valeur,_ = Hashtbl.find htbl i in retour.(i) <- (Array.of_list valeur)
            done;
            retour;
    and aux3 = fun htbl ->
        let retour = Array.make (Hashtbl.length htbl) ""
        in
            for i = 0 to (Array.length retour)-1 do
                let valeur = Hashtbl.find htbl i in retour.(i) <- valeur
            done;
            retour;
    in
  (*routine internes utilisées*)
        let engendre_affiche_tableau = fun fonction fin ->
        [Ast2.Ifte
          (Ast2.Eq (Ast2.Variable_entier (0, 1), Ast2.Const_entier 1),
          [Ast2.WriteString 2;
           Ast2.Affectation_entier ((0, 3),
            Ast2.Acces_tableau_entier ((0, 0),
             Ast2.Plus
              (Ast2.Fois
                (Ast2.Moins (Ast2.Variable_entier (0, 0),
                  Ast2.Const_entier 0),
                Ast2.Const_entier 4),
              Ast2.Const_entier 0)));
           fonction 3; fin 3],
          [Ast2.WriteString 2;
           Ast2.Affectation_entier ((0, 4),
            Ast2.Acces_tableau_entier ((0, 0),
             Ast2.Plus
              (Ast2.Fois
                (Ast2.Moins (Ast2.Variable_entier (0, 0),
                  Ast2.Const_entier 0),
                Ast2.Const_entier 4),
              Ast2.Const_entier 0)));
           fonction 4;
           Ast2.Boucle (2,
            Ast2.Plus (Ast2.Variable_entier (0, 0), Ast2.Const_entier 1),
            Ast2.Moins
             (Ast2.Plus (Ast2.Variable_entier (0, 0),
               Ast2.Variable_entier (0, 1)),
             Ast2.Const_entier 1),
            1,
            [Ast2.WriteString 4;
             Ast2.Affectation_entier ((0, 5),
              Ast2.Acces_tableau_entier ((0, 0),
               Ast2.Plus
                (Ast2.Fois
                  (Ast2.Moins (Ast2.Variable_entier (0, 2),
                    Ast2.Const_entier 0),
                  Ast2.Const_entier 4),
                Ast2.Const_entier 0)));
             fonction 5]);
           fin 3])] in



        let ast2,t,s = analyse ast in match ast2 with
            Some(ast3) -> {Ast2.corps = aux ast3; Ast2.tableauConsEnt = aux2 t; Ast2.tableauString = aux3 s; Ast2.globale =
[|
  {Ast2.fonId = [-1]; Ast2.fonEnt = 4; Ast2.fonNbEntParam = 3;
       Ast2.fonTab = [|3; 3|]; Ast2.fonNbTabParam = 2;
       Ast2.fonSous_proc = [||];
       Ast2.fonCode =
        [Ast2.Boucle (3, Ast2.Const_entier 0,
          Ast2.Moins (Ast2.Variable_entier (0, 2), Ast2.Const_entier 1), 1,
          [Ast2.Affectation_tae ((0, 0),
            Ast2.Plus
             (Ast2.Fois
               (Ast2.Plus (Ast2.Variable_entier (0, 3), Ast2.Variable_entier (0, 0)),
               Ast2.Const_entier 4),
             Ast2.Const_entier 0),
            Ast2.Acces_tableau_entier ((0, 1),
             Ast2.Plus
              (Ast2.Fois
                (Ast2.Moins (Ast2.Variable_entier (0, 3), Ast2.Variable_entier (0, 1)),
                Ast2.Const_entier 4),
              Ast2.Const_entier 0)))])]};

 {Ast2.fonId = [-2]; Ast2.fonEnt = 6; Ast2.fonNbEntParam = 2;
       Ast2.fonTab = [|3|]; Ast2.fonNbTabParam = 1; Ast2.fonSous_proc = [||];
       Ast2.fonCode = engendre_affiche_tableau (fun i -> Ast2.WriteInt i) (fun i -> Ast2.WriteString i)};
 {Ast2.fonId = [-3]; Ast2.fonEnt = 6; Ast2.fonNbEntParam = 2;
       Ast2.fonTab = [|3|]; Ast2.fonNbTabParam = 1; Ast2.fonSous_proc = [||];
       Ast2.fonCode = engendre_affiche_tableau (fun i -> Ast2.WriteInt i) (fun i -> Ast2.WritelnString i)};
{Ast2.fonId = [-4]; Ast2.fonEnt = 1; Ast2.fonNbEntParam = 1;
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode =
        [
            Ast2.Ifte(Ast2.Variable_booleen (0,0), [Ast2.WriteString 0], [Ast2.WriteString 1]);
        ]};
{Ast2.fonId = [-5]; Ast2.fonEnt = 1; Ast2.fonNbEntParam = 1;
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode =
        [
            Ast2.Ifte(Ast2.Variable_booleen (0,0), [Ast2.WritelnString 0], [Ast2.WritelnString 1]);
        ]};
 {Ast2.fonId = [-6]; Ast2.fonEnt = 6; Ast2.fonNbEntParam = 2;
       Ast2.fonTab = [|3|]; Ast2.fonNbTabParam = 1; Ast2.fonSous_proc = [||];
       Ast2.fonCode = engendre_affiche_tableau (fun i -> Ast2.AppelProc([-4],[i],[]))  (fun i -> Ast2.WriteString i)};
 {Ast2.fonId = [-7]; Ast2.fonEnt = 6; Ast2.fonNbEntParam = 2;
       Ast2.fonTab = [|3|]; Ast2.fonNbTabParam = 1; Ast2.fonSous_proc = [||];
       Ast2.fonCode = engendre_affiche_tableau (fun i -> Ast2.AppelProc([-4],[i],[]))  (fun i -> Ast2.WritelnString i)};
 {Ast2.fonId = [-8]; Ast2.fonEnt = 1; Ast2.fonNbEntParam = 1;
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode = [Ast2.WriteInt 0;]};
 {Ast2.fonId = [-9]; Ast2.fonEnt = 1; Ast2.fonNbEntParam = 1;
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode = [Ast2.WritelnInt 0;]};
 {Ast2.fonId = [-10]; Ast2.fonEnt = 2; Ast2.fonNbEntParam = 2; (*create*)
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode = []};
 {Ast2.fonId = [-11]; Ast2.fonEnt = 1; Ast2.fonNbEntParam = 1; (*delete*)
       Ast2.fonTab = [||]; Ast2.fonNbTabParam = 0; Ast2.fonSous_proc = [||];
       Ast2.fonCode = []};
|]

}
            |None -> raise (InconsistenceAnalyseStatique 1)

