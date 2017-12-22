let drg = 8;; (* debut des registres generiques*)
let drio = 2;; (* debut des registres io*)
let tmp = 29;;
let tmp2 = 28;;
let tmp3 = 27;;
let fp = 30;;
let ra = 31;;
let fpm = 0;;
let ram = 4;;

type inference =  Tableau of (int*int)
                 |Entier of Ast4.parametre
                 |Move of int

exception InconsistenceGeneration

(*fournit la taille d'enregistrement nécéssaire à fo*)
let taille_enregistrement = fun fo -> let retour = ref fo.Ast5.piletab in for i = fo.Ast5.nbTablParam to (Array.length fo.Ast5.tab) - 1 do retour := !retour + 4*fo.Ast5.tab.(i) done; !retour;;

(*prend un programme et le transforme*)
let genere_code = fun p ->
  (*référence les fonctions dans une table et décore les fonctions*)
  let programme2 = Ast45.transforme_programme p in
    let rec compile_fonction = fun pr fonction ->
      (*cas particulier de Create and Free*)
      if fonction.Ast5.id = [-10] then
        Printf.sprintf "f%s:\n\tmove $%d,$%d\n\tjal Create\n\tmove $%d,$%d\n\tjr $%d\n" fonction.Ast5.nom tmp ra ra tmp ra
      else if fonction.Ast5.id = [-11] then
        Printf.sprintf "f%s:\n\tmove $%d,$%d\n\tjal Free\n\tmove $%d,$%d\n\tjr $%d\n" fonction.Ast5.nom tmp ra ra tmp ra
      else

      (*associe à un no de registre son numéro effectif*)
      let rec nor = fun r -> r + drg

      (*indique l'adresse d'une sauvegarde, sous la forme profondeur,offset vis-à-vis de fp la plupart du temps*)
      and addrs = fun r ->
        match r with
           Ast4.RegistreVirtuel i -> (0,fonction.Ast5.pilerv+4*i)
          |Ast4.RegistreStatique i -> (0,fonction.Ast5.pilers+4*i)
          |Ast4.RegistreMere (p,i) ->
              let fonction_mere,nom = Hashtbl.find programme2.Ast5.principal ((Ast45.enleve_tete fonction.Ast5.id (p)))
              in
                (p,fonction_mere.Ast5.pilers+4*i)
          |Ast4.RegistreIO (i) when i >= 6 -> (-1,fonction.Ast5.pileio+4*(i-6))
          |Ast4.RegistreIO (i) -> (-2,i+drio)

      (*recupere l'adresse d'un tableau*)
      and addrt = fun fo p i -> 
        let rec addrtaux = fun fonction i ->
          let retour = ref 0
          in
            for j = 0 to i
              do retour := !retour + fonction.Ast5.tab.(j)
            done;
            !retour-1
      
        and addrtauxcons = fun i ->
          let retour = ref 0
          in
            for j = 0 to i-1
              do retour := !retour + Array.length(programme2.Ast5.tableauConsEnt.(j))
            done;
            !retour
        in
          if (p >= 0)
          then
            0,(addrtaux fo i)
          else
            -1,(addrtauxcons i)

      (*resoud les cycles de paramèrtres io*)                       
      and resoud_inf = fun tabtab tabreg nb flux ->
        let lgtab = (Array.length tabtab)
        and lgreg = (Array.length tabreg)
        in
          let lg = lgtab+lgreg
          in
            let retour = Array.create (6*lg) (-1,Move 42)
            and inf = Array.create (6*lg) (-1,42)
            in
              let pas_ecrit = fun s -> let r = ref true in for i = lg to 2*lg-1 do let d,_ = inf.(i) in if d=s then r:=false done; !r
              and pas_lu = fun d -> let r = ref true in for i = lg to 2*lg-1 do let _,s = inf.(i) in if d=s then r:=false done; !r
              and cherche = fun s -> let r = ref (-1) in for i = lg to 2*lg-1 do let d,_ = inf.(i) in if d=s then r:=i done; !r
              and switch = fun tab i j -> let tmp = tab.(i) in tab.(i) <- tab.(j); tab.(j) <- tmp;
              and switch2 = fun tab i j -> let tmp = tab.(i) in tab.(i) <- tab.(j); tab.(j) <- tmp;
              and debut = ref 0
              and debut2 = ref (1*lg)
              and debut3 = ref (5*lg)
              and nombre_affectation = ref 42
              and nombre_restants = ref 0 in
                for i = 0 to lgreg-1 do
                  match tabreg.(i) with
                     Ast4.ParamIO(no) as k when i < 6 && no < 6 ->
                       retour.(!debut2) <- i,(Entier k);
                       inf.(!debut2) <- i,no;
                       incr debut2
                    |Ast4.ParamIO(no) as k when no < 6 ->
                       retour.(!debut) <- i,(Entier k);
                       incr debut
                    |_ as k ->
                       retour.(!debut3) <- i,Entier(k);
                       incr debut3
                done;
              
                (*tous les registres qui ne sont pas embêtants sont mis de côté*)
                for i = 0 to lgtab-1 do
                  match tabtab.(i) with
                     (0,no) as k when no < nb && (i+lgreg) < 6 && no < 6 ->
                        retour.(!debut2) <- (i+lgreg),(Tableau k);
                        inf.(!debut2) <- (i+lgreg),no;
                        incr debut2
                    |(0,no) as k when no < nb &&                  no < 6 ->
                        retour.(!debut) <- (i+lgreg),(Tableau k); 
                        incr debut
                    |(p,no) as k -> 
                        retour.(!debut3) <- (i+lgreg),(Tableau k);
                        incr debut3
                done;

                (*tous les registres qui ne sont pas embêtants sont mis de côté*)
                debut3 := 5*lg;
                while (!nombre_affectation <> 0)
                do
                  nombre_affectation := 0;
                  for i = lg to 2*lg - 1 do
                    let d,s = inf.(i) in
                      if d <> -1 && pas_ecrit s then
                        begin
                          decr debut3;
                          switch retour i !debut3;
                          switch2 inf i !debut3;
                          incr nombre_affectation;
                        end;

                      if d <> -1 && pas_lu d then
                        begin
                          switch retour i !debut;
                          switch2 inf i !debut;
                          incr debut;
                          incr nombre_affectation;
                        end;
                  done;                
                done;

                for i = lg to 2*lg - 1 do
                  if fst (inf.(i)) <> -1 then incr nombre_restants;
                done;
                debut := 2*lg;  

                (*casse les cycles*)
                while (!nombre_restants > 0) do
                  let dernier_different = ref (-1) in
                    for i = lg to 2*lg-1 do
                      let d,_ = inf.(i) in
                        if d<> -1 then dernier_different := i;
                    done;
                    let d',s' = inf.(!dernier_different) in
                      retour.(!debut) <- tmp,Move(s'+drio);
                      incr debut;
                      let i = ref (cherche s') in
                        while (!i <> !dernier_different) do
                          let d,s = inf.(!i) in
                            switch retour !debut !i;
                            switch2 inf !debut !i;
                            incr debut;
                            decr nombre_restants;
                            i := cherche s; 
                        done;
                        decr nombre_restants;
                        retour.(!debut) <- d'+drio,Move(tmp);
                        incr debut;
                done;
                retour

      (*...*)
      and string_of_binop = fun bin -> match bin with
           Ast4.Fois -> "mul"
          |Ast4.Plus -> "add"
          |Ast4.Moins -> "sub"
          |Ast4.Div -> raise InconsistenceGeneration
          |Ast4.Modulo -> "rem"
          |Ast4.Nor -> "nor"
          |Ast4.Xor -> "xor"
          |Ast4.Et -> "and"
          |Ast4.Ou -> "or"

      and string_of_binopi = fun bin -> match bin with
           Ast4.Addi -> "addi"
          |Ast4.Andi -> "andi"
          |Ast4.Xori -> "xori"
          |Ast4.Ori -> "ori"

      and string_of_uniop = fun un -> match un with
           Ast4.Not -> "not"
          |Ast4.Neg -> "neg"

      (*remonte les enregistrements*)
      and recupere_fp_mere = fun remonte dest ->
        let retour = ref "" in            
          retour := !retour ^ Printf.sprintf "\tmove $%d,$%d\n" dest fp;
          if remonte>=0 then
            for i = 1 to remonte do
              retour := !retour ^ (Printf.sprintf "\tlw $%d,%d($%d)\n" dest fpm dest);
            done;
          !retour
          
      and sub_list = fun l i -> match l,i with _,0 -> l | (a::r),_ -> sub_list r (i-1) | [],_ -> failwith "sub_list aie"

      (*recupere l'adresse d'un tableau*)
      and recupere_adresse_tableau = fun (p2,i2) dest -> let r = 
        begin
         match (p2,i2) with
           (-2,i2) -> Printf.sprintf "\tmove $%d,$%d\n" dest (drio+i2)
          |(0,i2)  when i2 < fonction.Ast5.nbTablParam
                     && i2+fonction.Ast5.nbEntParam < 6  -> Printf.sprintf "\tmove $%d,$%d\n" dest (i2+drio+fonction.Ast5.nbEntParam)
          |(0,i2)  when i2 < fonction.Ast5.nbTablParam   -> Printf.sprintf "\tlw $%d,-%d($%d)\n" dest (fonction.Ast5.pileio + 4*(i2-6)) fp;
          |(0,i2)                                        -> let (p,i) = addrt fonction p2 i2 in Printf.sprintf "\taddi $%d,$%d,-%d\n" dest fp (fonction.Ast5.piletab+4*i)
          |(-1,i2)                                       -> Printf.sprintf "\tla $%d,tc%d\n" dest i2
          |(p2,i2)                                       ->
          let ancetre,_ = Hashtbl.find pr.Ast5.principal (sub_list fonction.Ast5.id p2) in 
            let (p,i) = addrt ancetre p2 i2 and retour = ref "" in
              begin
                retour := !retour ^ recupere_fp_mere p tmp;
                retour := !retour ^ (
                match i2 with
                   i3 when i3 < ancetre.Ast5.nbTablParam && i3+ancetre.Ast5.nbEntParam < 6 -> Printf.sprintf "\tlw %d,%d(%d)\n" dest (ancetre.Ast5.pilesauv+4*i3) tmp
                  |i3 when i3 < ancetre.Ast5.nbTablParam -> Printf.sprintf "\tlw %d,%d(%d)\n" dest (ancetre.Ast5.pileio+4*ancetre.Ast5.nbEntParam+4*(i3-6)) tmp
                  |i3 -> Printf.sprintf "\taddi $%d,$%d,-%d\n" dest tmp (ancetre.Ast5.piletab+4*i);)
              end;
              !retour;
          end in r;

      (*genere le code associé à une instruction*)
      and generation_code = fun pr g -> match g with
           Ast4.Writeint(d) -> Printf.sprintf "\tmove $%d,$v0\n\tmove $%d,$a0\n\tli $v0,1\n\tmove $a0,$%d\n\tsyscall\n\tmove $a0,$%d\n\tmove $v0,$%d\n" tmp tmp2 (nor d) tmp2 tmp
          |Ast4.Exit -> Printf.sprintf "\tli $v0,10\n\tsyscall\n"
          |Ast4.Writestring(s) -> Printf.sprintf "\tmove $%d,$v0\n\tmove $%d,$a0\n\tli $v0,4\n\tla $a0,s%d\n\tsyscall\n\tmove $a0,$%d\n\tmove $v0,$%d\n" tmp tmp2 s tmp2 tmp
          |Ast4.Writelnint(d) -> Printf.sprintf "\tmove $%d,$v0\n\tmove $%d,$a0\n\tli $v0,1\n\tmove $a0,$%d\n\tsyscall\n\tli $v0,4\n\tla $a0,s5\n\tsyscall\n\tmove $a0,$%d\n\tmove $v0,$%d\n" tmp tmp2 (nor d) tmp2 tmp
      (*la chaine constante n°d est situé au label sd*)
          |Ast4.Writelnstring(s) -> Printf.sprintf "\tmove $%d,$v0\n\tmove $%d,$a0\n\tli $v0,4\n\tla $a0,s%d\n\tsyscall\n\tli $v0,4\n\tla $a0,s5\n\tsyscall\n\tmove $a0,$%d\n\tmove $v0,$%d\n" tmp tmp2 s tmp2 tmp
          |Ast4.Binop(Ast4.Div,d,a,b) -> Printf.sprintf "\tbeqz $%d,affiche_erreur\n\tdiv $%d,$%d,$%d\n" (nor b) (nor d) (nor a) (nor b)
          |Ast4.Binop(bin,d,a,b) -> Printf.sprintf "\t%s $%d,$%d,$%d\n" (string_of_binop bin) (nor d) (nor a) (nor b)
          |Ast4.Binopi(bin,d,a,i) -> Printf.sprintf "\t%s $%d,$%d,$%d\n" (string_of_binopi bin) (nor d) (nor a) i
          |Ast4.Uniop(un,d,s) -> Printf.sprintf "\t%s $%d,$%d\n" (string_of_uniop un) (nor d) (nor s)
          |Ast4.Mov(d,s) -> Printf.sprintf "\tmove $%d,$%d\n" (nor d) (nor s)
          (*manipulation des sauvegarde*)
          |Ast4.Movrs(d,s) ->
            let (p,i) = addrs s
            in
              if p = -2 then
                Printf.sprintf "\tmove $%d,$%d\n" (nor d) i                            
              else if p = -1 then
                Printf.sprintf "\tlw $%d,-%d($%d)\n" (nor d) i fp
              else if p = 0 then
                Printf.sprintf "\tlw $%d,-%d($%d)\n" (nor d) i fp
              else
                begin
                  let retour = ref "" in
                    (*remonte*)
                    retour := !retour ^ recupere_fp_mere p tmp;
                    retour := !retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n" (nor d) i tmp);
                    !retour;
                end;
          |Ast4.Movi(s,d) -> Printf.sprintf "\tli $%d,%d\n" (nor s) d
          |Ast4.Movsr(s,d) ->
            let (p,i) = addrs s
            in
              if p = -2 then
                Printf.sprintf "\tmove $%d,$%d\n" i (nor d)
              else if p = -1 then
                Printf.sprintf "\tsw $%d,-%d($%d)\n" (nor d) i fp
              else if p = 0 then
                Printf.sprintf "\tsw $%d,-%d($%d)\n" (nor d) i fp
              else
                begin
                  let retour = ref "" in
                    retour := !retour ^ recupere_fp_mere p tmp;
                    retour := !retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n" (nor d) i tmp);
                    !retour;
                end;
          (*utilisation des tableaux*)
          |Ast4.Movrt(dest,tab,indice) ->
              (recupere_adresse_tableau tab tmp)
            ^ (Printf.sprintf "\tadd $%d,$%d,$%d\n\tlw $%d,%d($%d)\n" tmp tmp (nor indice) (nor dest) 0 tmp);
          |Ast4.Movtr(tab,indice,source) ->
              (recupere_adresse_tableau tab tmp)
            ^ (Printf.sprintf "\tadd $%d,$%d,$%d\n\tsw $%d,%d($%d)\n" tmp tmp (nor indice) (nor source) 0 tmp);
          
          |Ast4.Movaddr (dest, tab, indice) ->
              (recupere_adresse_tableau tab tmp)
            ^ (Printf.sprintf "\tadd $%d,$%d,$%d\n" (nor dest) tmp (nor indice));

          |Ast4.Movrrf (dest,source) -> Printf.sprintf "\tlw $%d,($%d)\n" (nor dest) (nor source)
          |Ast4.Movrfr (source,dest) -> Printf.sprintf "\tsw $%d,($%d)\n" (nor dest) (nor source)
          |Ast4.Read (d) -> Printf.sprintf "\tmove $%d,$v0\n\tli $v0,5\n\tsyscall\n\tmove $%d,$v0\n\tmove $v0,$%d\n" tmp (nor d) tmp

          (*le label n°i de la fonction s s'appelle jsji*)
          |Ast4.Jump(lbl) -> Printf.sprintf "\tj j%sj%d\n" fonction.Ast5.nom lbl 
          |Ast4.Label(lbl) -> Printf.sprintf "j%sj%d:\n" fonction.Ast5.nom lbl

          |Ast4.CJumpb(lbl,r) -> Printf.sprintf "\tbnez $%d,j%sj%d\n" (nor r) fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.Eq) -> Printf.sprintf "\tbeq $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.Neq) -> Printf.sprintf "\tbne $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.SEq) -> Printf.sprintf "\tbge $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.IEq) -> Printf.sprintf "\tble $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.Sup) -> Printf.sprintf "\tbgt $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.CJump(lbl,a,b,Ast4.Inf) -> Printf.sprintf "\tblt $%d,$%d,j%sj%d\n" (nor a) (nor b)  fonction.Ast5.nom lbl
          |Ast4.AppelProc(id, sr, st) ->
            let retour = ref "\n"
            and tabreg = Array.of_list sr
            and tabtab = Array.of_list st
            and new_fo,new_nom = Hashtbl.find pr.Ast5.principal id
            in
            let lgreg = (Array.length tabreg)
            and lgtab = (Array.length tabtab)
            in              
            let tabinf = resoud_inf tabtab tabreg fonction.Ast5.nbTablParam retour
            and taille = taille_enregistrement fonction
            in
              (*enregistre dans la pile les ios actuels*)
              for i = 0 to min 5 (lgreg+lgtab - 1) do
                retour := !retour ^ Printf.sprintf "\tsw $%d,-%d($%d)\n" (drio+i) (fonction.Ast5.pilesauv+4*i) fp;
              done;

              (*passe effectivement les paramètres*)
              for j = 0 to (Array.length tabinf) -1 do
                match tabinf.(j) with
                    -1,_ -> ();
                   |i,(Entier e) ->
                      begin
                        match e with
                          Ast4.ParamIO(no) when no < 6 && i<6 ->
                            retour:=!retour ^ (Printf.sprintf "\tmove $%d,$%d\n" (drio+i) (drio+no))
                        
                         |Ast4.ParamIO(no) when no < 6        ->
                            retour:=!retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n"
                                                              (drio+no)
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)

                         |Ast4.ParamIO(no) when i< 6          ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pileio+4*(no-6))
                                                              fp)

                         |Ast4.ParamIO(no)                    ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (fonction.Ast5.pileio+4*(no-6))
                                                              fp
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)

                         |Ast4.ParamStatique(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pilers+4*no)
                                                              fp)

                         |Ast4.ParamStatique(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (fonction.Ast5.pilers+4*no)
                                                              fp
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)

                         |Ast4.ParamVirtuel(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pilerv+4*no)
                                                              fp)

                         |Ast4.ParamVirtuel(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (fonction.Ast5.pilerv+4*no)
                                                              fp
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)

                         |Ast4.ParamGeneral(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tmove $%d,$%d\n"
                                                              (drio+i)
                                                              (nor no))

                         |Ast4.ParamGeneral(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n"
                                                              (nor no)
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)
                      end;
                  
                   |i,Tableau(t) ->
                      begin
                        match t with
                          |k when i < 6 ->
                           retour :=   !retour
                                     ^ (recupere_adresse_tableau k (drio+i))
                          |k ->
                           retour :=   !retour
                                     ^ (recupere_adresse_tableau k tmp)
                                     ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n" tmp (new_fo.Ast5.pileio+4*(i-6)-taille) fp)
                      end;
                   |i,Move(t) ->
                      retour :=   !retour
                                ^ Printf.sprintf "\tmove $%d,$%d\n" i t
              done;

              (*recupere le fp de la mere de la fonction appellee*)
              retour := !retour ^ recupere_fp_mere (1+(List.length fonction.Ast5.id)-(List.length id)) tmp;
             
              retour := !retour ^ Printf.sprintf "\tsw $%d,-%d($%d)\n" tmp (fpm+taille) fp;
              retour := !retour ^ Printf.sprintf "\tsw $%d,-%d($%d)\n" ra ram fp;

              (*decale fp*)
              retour := !retour ^ Printf.sprintf "\taddi $%d,$%d,-%d\n" fp fp taille;

              retour := !retour ^ Printf.sprintf "\tjal f%s\n" new_nom;

              retour := !retour ^ Printf.sprintf "\taddi $%d,$%d,%d\n" fp fp taille;

              retour := !retour ^ Printf.sprintf "\tlw $%d,-%d($%d)\n" ra ram fp;

              (*restore les paramètres entiers ou booléens passés en paramètres*)
                for j = (Array.length tabinf) -1 downto 0 do
                match tabinf.(j) with
                    -1,_ -> ();
                   |i,(Entier e) ->
                      begin
                        match e with
                          Ast4.ParamIO(no) when no < 6 && i<6 ->
                            retour:=!retour ^ (Printf.sprintf "\tmove $%d,$%d\n" (drio+no) (drio+i))
                        
                         |Ast4.ParamIO(no) when no < 6        ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n"
                                                              (drio+no)
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)

                         |Ast4.ParamIO(no) when i< 6          ->
                            retour:=!retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pileio+4*(no-6))
                                                              fp)

                         |Ast4.ParamIO(no)                    ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp
                                                              tmp
                                                              (fonction.Ast5.pileio+4*(no-6))
                                                              fp)

                         |Ast4.ParamStatique(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pilers+4*no)
                                                              fp)

                         |Ast4.ParamStatique(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp
                                                              tmp
                                                              (fonction.Ast5.pilers+4*no)
                                                              fp)

                         |Ast4.ParamVirtuel(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tsw $%d,-%d($%d)\n"
                                                              (drio+i)
                                                              (fonction.Ast5.pilerv+4*no)
                                                              fp)

                         |Ast4.ParamVirtuel(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n\tsw $%d,-%d($%d)\n"
                                                              tmp
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp
                                                              tmp
                                                              (fonction.Ast5.pilerv+4*no)
                                                              fp)

                         |Ast4.ParamGeneral(no) when i < 6 ->
                            retour:=!retour ^ (Printf.sprintf "\tmove $%d,$%d\n"
                                                              (nor no)
                                                              (drio+i))

                         |Ast4.ParamGeneral(no)            ->
                            retour:=!retour ^ (Printf.sprintf "\tlw $%d,-%d($%d)\n"
                                                              (nor no)
                                                              (new_fo.Ast5.pileio+4*(i-6)+taille)
                                                              fp)
                      end;

                   |i,Move(t) ->
                      retour :=   !retour
                                ^ Printf.sprintf "\tmove $%d,$%d\n" t i
                   |_ -> ();
              done;

              (*restore les ios pre appel*)
              for i = 0 to min 5 (lgreg+lgtab - 1) do
                retour := !retour ^ Printf.sprintf "\tlw $%d,-%d($%d)\n" (drio+i) (fonction.Ast5.pilesauv+4*i) fp;
              done;

              retour := !retour ^ (Printf.sprintf "\n");
              !retour

in
   Printf.sprintf "f%s:\n%s\tjr $%d\n"
                  fonction.Ast5.nom
                  (List.fold_left (fun suite instruction -> suite^(generation_code pr instruction)) "" fonction.Ast5.corps)
                  ra

in let
  corps = Hashtbl.fold (fun chemin (fonction,nom) continuation -> continuation^(compile_fonction programme2 fonction)) programme2.Ast5.principal ""
  in
(*genere preambule et postbule*)
    Printf.sprintf ".data\n%serr_div0:.asciiz \"erreur d'arithmétique\\n\"\n%s.text\n.globl main\n%smain:\n\taddi $%d,$sp,%d\n\tjal f0\n\tli $v0,10\n\tsyscall\n%s%s"
        (List.fold_left (fun retour (s,i) -> (Printf.sprintf "s%d : .asciiz \"%s\"\n" i s)^retour) "" (Array.to_list (Array.mapi (fun i a -> (a,i)) programme2.Ast5.tableauString)))
        (List.fold_left (fun retour (t,i) -> (Printf.sprintf "tc%d : .word %s\n" i (Array.fold_left (fun s i -> Printf.sprintf "%d,%s" i s) "0"  t))^retour) "" (Array.to_list (Array.mapi (fun i a -> (a,i)) programme2.Ast5.tableauConsEnt)))
        (Printf.sprintf "affiche_erreur:\n\tli $v0,4\n\tla $a0,err_div0\n\tsyscall\n\tli $v0,10\n\tsyscall\n")
        fp (-4)
        corps

(*allocation dynamique*)
"# Allocation dynamique
# La structure est une liste doublement chaînée, chaque bloc possède une entête du type
# Bloc Libre : 0, Bloc utilisé : -1 ,                       ---- 4 octets
# Pointeur_haut : Si dernier bloc, mettre 0                 ---- 4 octets
# Pointeur_bas  : Si premier bloc, mettre 0                 ---- 4 octets

# ENTREE : $3,taille, SORTIE : $2 valeur retour (pointeur vers le haut du bloc)
# Registres détruits : $28,$27 	

Create:
	la $28, debut_tas                                # $28 le pointeur vers le bloc qu'on est en train de regarder
	addi $28,$28,8

cherche:
	lw $27,($28)                                       #le bloc est-il libre?

	beqz $27,verif_taille

	b passe_bloc_suivant


verif_taille:
	lw $27,-4($28)

	beqz $27,change_dernier_bloc                      # on était au dernier bloc, la taille est infini

	sub $27,$27,$28
	addi $27,$27,-12                                   # $27 est la taille du bloc en cours

	bge $27,$3,change_bloc

	b passe_bloc_suivant

change_dernier_bloc:
	move $2,$28                                        # on met dans le registre de retour la valeur attendue
	li $27,-1                     
	sw $27,($28)                                       # on met à jour le flag du bloc, car il est utilisé maintenant

	add $27,$28,$3           
	addi $27,$27,12                                

	sw $28,-8($27)                                     # On met à jour l'adresse du pointeur_bas du nouveau bloc
	li $28,0
	sw $28,-4($27)                                     # On met à jour le pointeur_haut (0)
	sw $28,($27)                                       # On dit que ce bloc est libre (0)

	sw $27,-4($2)                                     # On met à jour le pointeur_haut du bloc qui nous intéresse

	b fin


change_bloc:
	li $27,-1                                         # mise à jour du bloc
	sw $27,($28)
	move $2,$28

	b fin

fin:
	addi $2,$2,4
	jr $ra

passe_bloc_suivant:
	lw $28,-4($28)
	b cherche




	
# ENTREE : $2 pointeur SORTIE : Le bloc à l'adresse $2 est dit comme libre
# Registres détruits : $27,$28
	
Free:

	li $27,0
	sw $27,-4($2)                              #On dit que le bloc est libre, c'est génial !


#on teste si le bloc du haut est libre?

	lw $27,-8($2)
	lw $28,($27)
	beqz $28,compacte_haut

suite:

	lw $27,-12($2)
	beqz $27,fin2

	lw $28,($27)
	beqz $28,compacte_bas
	
	b fin2




compacte_haut:
	lw $28,-4($27)
	beqz $28,cas_particulier_compacte_haut
	
	sw $28,-8($2)

	move $27,$2
	addi $27,$27,-4
	sw $27,-8($28)

	b suite


cas_particulier_compacte_haut:
	li $27,0
	sw $27,-8($2)
	b suite
	

compacte_bas:
	lw $28,-8($2)
	beqz $28,cas_particulier_compacte_bas
	
	sw $28,-4($27)
	sw $27,-8($28)

	b fin2


cas_particulier_compacte_bas:
	li $28,0
	sw $28,-4($27)

	
fin2:
	jr $ra


debut_tas:
.data 
.word 0,0,-1
"

