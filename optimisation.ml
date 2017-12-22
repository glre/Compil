open Ast4

let z = ref 0;;

let rec optimise_code = fun l3 -> match l3 with

   (Mov (17,i))::(Mov(j,17))::l when i=j -> incr z; optimise_code l
  |(Mov (17,i))::(Mov(j,17))::l -> incr z; (Mov(j,i))::(optimise_code l)
  |(Mov (17,i))::k::(Binop(bin,d,17,b))::l -> incr z; optimise_code (k::(Binop(bin,d,i,b))::l)
  |(Mov (18,i))::(Binop(bin,d,a,18))::l -> incr z; optimise_code ((Binop(bin,d,a,i))::l)
  |(Mov (17,i))::k::(Binopi(bin,d,17,b))::l -> incr z; optimise_code (k::(Binopi(bin,d,i,b))::l)
  |(Binop (bin,17,a,b))::Mov(i,17)::l -> incr z; (Binop (bin,i,a,b))::(optimise_code l)
  |(Binopi (bin,17,a,b))::Mov(i,17)::l -> incr z; (Binopi (bin,i,a,b))::(optimise_code l)
  |(Mov (17,i))::(Uniop(un,d,17))::l -> incr z; optimise_code ((Uniop(un,d,i))::l)
  |(Uniop(un,17,d))::(Mov (i,17))::l -> incr z; (Uniop(un,i,d))::(optimise_code l)
  |(Movi(17,k))::(Mov (i,17))::l -> incr z; (Movi (i,k))::(optimise_code l)
  |(Mov(17,i))::(Movrt(a,k,17))::l -> incr z; optimise_code ((Movrt(a,k,i))::l)
  |(Movrt(17,k,a))::(Mov (i,17))::l -> incr z; (Movrt(i,k,a))::(optimise_code l)
  |(Mov (17,i))::k::(Movtr(u,b,17))::l -> incr z; optimise_code (k::(Movtr(u,b,i))::l)
  |(Mov (18,i))::(Movtr(u,18,b))::l -> incr z; Movtr(u,i,b)::(optimise_code l)
  | (a::r)->incr z; a::(optimise_code r)
  |[] -> []
and optimise_fonction = fun l2 -> match l2 with
        {id = id;
         nbRegistreVirtuel = nbRegistreVirtuel;
         nbRegistreStatique = nbRegistreStatique;
         nbEntParam =  nbEntParam;
         nbTablParam = nbTablParam;
         tab = tab;
         filles = filles;
         corps = corps} ->
        {id = id;
         nbRegistreVirtuel = nbRegistreVirtuel;
         nbRegistreStatique = nbRegistreStatique;
         nbEntParam =  nbEntParam;
         nbTablParam = nbTablParam;
         tab = tab;
         filles = Array.map optimise_fonction filles;
         corps = optimise_code corps}

and optimise = fun l1 -> match l1 with
 {tableauConsEnt = tableauConsEnt;
  tableauString = tableauString;
  principal = principal;
  globale = globale} ->
 {tableauConsEnt = tableauConsEnt;
  tableauString = tableauString;
  principal = optimise_fonction principal;
  globale = Array.map optimise_fonction globale},!z;;




