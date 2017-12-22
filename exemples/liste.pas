program main;
var g : ref of integer;
      
function creer_liste:ref of integer;
begin
   creer_liste := @(0);
end;

procedure ajoute_element_debut(var a : ref of integer; e : integer);
var n : ref of integer;
begin 
   n := new(2);
   !(n) := e;
   !(n+1) := ^(a);
   a := n;   
end; 

procedure supprime_element_debut(var a : ref of integer);
var c : ref of integer;
begin 
   if !(a)=0 then exit else begin c:= a; free(a);a := @(!(c+1)); end;
end; 

procedure affiche_liste(a : ref of integer);
begin
   if ^(a) <> 0 do begin writeln !(a),' ->',!(a+1); affiche_liste(@(!(a+1))); end;
end; 


function ajoute_element_trie(a : ref of integer; e : integer):ref of integer;
var r : ref of integer;
begin 
   if a=NULL then
   begin
      r := new(2);
      !(r):=e;
      !(r+1):=0;
      ajoute_element_trie:= r;
   end
   else
   begin
      if e <= !(a) then
      begin
	 r:=new(2);
	 !(r):=e;
	 !(r+1) := ^(a);
	 ajoute_element_trie := r;
      end
      else
      begin !(a+1) := ^(ajoute_element_trie(@(!(a+1)),e));
	 ajoute_element_trie := a;
      end;
   end;
end; { ajoute_element_trie }


function supprime_element_trie(a : ref of integer; e : integer):ref of integer;
var z : ref of integer;
begin
   if a = NULL then
   begin
      writeln 'element pas dans la liste, si cela se passe comme ca, je pars !'; exit;
   end
   else begin if e = !(a) then
   begin
      supprime_element_trie := @(!(a+1));
   end
   else
   begin
      !(a+1) := ^(supprime_element_trie(@(!(a+1)),e));
	 supprime_element_trie := a;
   end;
   end;
end;
   



var a : integer;
var i : integer;
begin 
   g:= creer_liste();
   writeln 'continuer? (1 pour ajouter un element, -1 pour supprimer un element, 0 pour quitter';
   a := read;
   while a <> 0 do
  begin
      if a=1 then begin
	 writeln 'valeur a inserer?';
	 i := read;
	 g :=ajoute_element_trie(g,i);
	 writeln 'liste:';
	 affiche_liste (g);
	 writeln 'continuer? (1 pour ajouter un element, -1 pour supprimer un element, 0 pour quitter';
	 a := read;
      end
     else begin
	 if a= -1 then begin
	    writeln 'valeur a supprimer?';
	 i := read;
	 g :=supprime_element_trie(g,i);
	 writeln 'liste:';
	 affiche_liste (g);
	 writeln 'continuer? (1 pour ajouter un element, -1 pour supprimer un element, 0 pour quitter';
	 a := read;
	 end
	 else begin writeln 'Mauvaise saisie. continuer? (1 pour ajouter un element, -1 pour supprimer un element, 0 pour quitter';
	    a := read;
	 end;
      end;
   end;
end.
