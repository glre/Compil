exception Enleve_tete

let rec construit_corps = fun {Ast4.principal = fon; Ast4.globale = glo} ->
  let tbl = Hashtbl.create 1 in
    let rec aux = fun fo -> match fo with {Ast4.id = id;
                                                     Ast4.nbRegistreVirtuel = nrv;
                                                     Ast4.nbRegistreStatique = nrs;
                                                     Ast4.nbEntParam = nbEntParam;
                                                     Ast4.nbTablParam = nbTablParam;
                                                     Ast4.tab = tailletab;
                                                     Ast4.filles = fi;
                                                     Ast4.corps = co} ->
                                          let ioreg = 6 (*min 6 (nbEntParam+nbTablParam)*)
                                          and pileio = max 0 (nbEntParam+nbTablParam-6) in
(*                                          Printf.printf "ioreg %s %d\n" (List.fold_left (fun s i -> s^(if i >= 0 then (string_of_int i) else "m"^(string_of_int (-i)))) "" id) ioreg;*)
                                          Hashtbl.add tbl id (                                            
                                            {Ast5.id = id; 
                                             Ast5.nom = List.fold_left (fun s i -> s^(if i >= 0 then (string_of_int i) else "m"^(string_of_int (-i)))) "" id;
                                             Ast5.pilesauv = 2*4;
                                             Ast5.pileio = 2*4+ioreg*4;
                                             Ast5.pilers = 2*4+ioreg*4+pileio*4;
                                             Ast5.pilerv = 2*4+ioreg*4+pileio*4+nrs*4;
                                             Ast5.piletab = 2*4+ioreg*4+pileio*4+nrs*4+nrv*4;
                                             Ast5.nbEntParam = nbEntParam;
                                             Ast5.nbTablParam = nbTablParam;
                                             Ast5.tab = tailletab;
                                             Ast5.corps = co},(List.fold_left (fun s i -> s^(if i >= 0 then (string_of_int i) else "m"^(string_of_int (-i)))) "" id));
                                         for i = 0 to (Array.length fi) - 1 do
                                            aux fi.(i);
                                         done;
    in aux fon ; for i = 0 to (Array.length glo) - 1 do aux glo.(i) done; (*Hashtbl.iter (fun _ (_,nom) -> Printf.printf " %s " nom) tbl;*) tbl
(*
and construit_instruction chemin = fun corps -> match corps with
    Ast4.Add(a,b,c) -> Ast5.Add(a,b,c)
   |Ast4.Sub(a,b,c) -> Ast5.Sub(a,b,c)
   |Ast4.Mul(a,b,c) -> Ast5.Mul(a,b,c)
   |Ast4.Div(a,b,c) -> Ast5.Div(a,b,c)
   |Ast4.Modulo(a,b,c) -> Ast5.Modulo(a,b,c)
   |Ast4.And(a,b,c) -> Ast5.And(a,b,c)
   |Ast4.Or(a,b,c) -> Ast5.Or(a,b,c)
   |Ast4.Nor(a,b,c) -> Ast5.Nor(a,b,c)
   |Ast4.Xor(a,b,c) -> Ast5.Xor(a,b,c)
   |Ast4.Addi(a,b,c) -> Ast5.Addi(a,b,c)
   |Ast4.Subi(a,b,c) -> Ast5.Subi(a,b,c)
   |Ast4.Andi(a,b,c) -> Ast5.Andi(a,b,c)
   |Ast4.Ori(a,b,c) -> Ast5.Ori(a,b,c)
   |Ast4.Xori(a,b,c) -> Ast5.Xori(a,b,c)
   |Ast4.Not(a,b) -> Ast5.Not(a,b)
   |Ast4.Neg(a,b) -> Ast5.Neg(a,b)
   |Ast4.Movi(a,b) -> Ast5.Movi(a,b)
   |Ast4.Mov(a,b) -> Ast5.Mov(a,b)
   |Ast4.Movrt(a,b,c) -> Ast5.Movrt(a,b,c)
   |Ast4.Movtr(a,b,c) -> Ast5.Movtr(a,b,c)
   |Ast4.Movrs(a,b) -> Ast5.Movrs(a,b)
   |Ast4.Movsr(a,b) -> Ast5.Movsr(a,b)
   |Ast4.Jump(lbl) -> Ast5.Jump(lbl)
   |Ast4.Label(lbl) -> Ast5.Label(lbl)
   |Ast4.CJump(a,b,c,d) -> Ast5.CJump(a,b,c,d)
   |Ast4.CJumpb(a,b) -> Ast5.CJumpb(a,b)
   |Ast4.Writestring(i) -> Ast5.Writestring(i)
   |Ast4.Writelnstring(i) -> Ast5.Writelnstring(i)
   |Ast4.AppelProc((p,no),sl,tl) -> Ast5.AppelProc(no::(enleve_tete chemin (p+1)),sl,tl)
    *)
and enleve_tete = fun l p -> match l,p with
(l,0) -> l;
|([],_) -> raise Enleve_tete;
|((a::b),p) -> enleve_tete b (p-1);

and transforme_programme = fun p -> match p with {Ast4.tableauConsEnt = t; Ast4.tableauString = s} -> {Ast5.tableauConsEnt = t; Ast5.tableauString = s; Ast5.principal = construit_corps p};;
