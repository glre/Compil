program main;
  const ii = (1,3);
{  const j : array [0..1] of array [0..1] of integer = ((0,0),(1,1)); "Ne marche pas, pas le temps"}
  var kk : array [0..1] of integer;
{ les affectations de tableaux bidimensionnels constants bugs }
  var rf : ref of integer;

function un(a,b: integer ):integer;

   function deux(c,d :  integer):integer;

      function trois(e,f :  integer):integer;

      begin
	       a:=4; {ne fait rien}
	       trois := e+f;
	 
      end; { trois }

   begin
      deux := trois(c,d);
   end; { deux }

begin
   un := deux(a,b);
    { est cense afficher 4, affiche 3; cela vient du fait est encore un probleme de registre statique, quand ils sont melanges avec des registres io}   writeln a;
   un := un + a;
end; { un }

var t1 : integer;
function torture : integer;
var t2 : integer;
function torture1 (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z : integer) : integer; {parfaitement fonctionnel, aucun problème de pile}
begin
  torture1 := (a+b+c+d+e+f+g+h+i+j+k+l+m+n+o+p+q+r+s+t+u+v+w+x+y+z)*t1*t2;
end;
begin
  t1 := read;
  t2 := read;
  torture := torture1(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26);
end;
begin
   t1 := 4;
   kk := ii;
   writeln kk;
   rf := &(kk);
   !(rf) := 4; 
   writeln kk;
   writeln un(3,4);
   writeln torture();
end.
