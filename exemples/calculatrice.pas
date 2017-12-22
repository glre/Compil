program main;
  var operation : integer;
  var tab : array [1..3] of integer;

  function calcule (i : integer; j : integer) : array [1..3] of integer;
  begin
    calcule[1] := i+j;
    calcule[2] := i-j;
    calcule[3] := i*j;
  end;

begin
  writeln 'operations : 1 +, 2 -, 3 *, 4 quitter';
  writeln 'notation prefixe : 1 1 2 -> 3';

  repeat
  begin
    operation := read;
    if (operation > 4) or (operation < 1) then writeln 'entre 1 et 4 svp'
    else if (operation <> 4) do
      begin
        tab := calcule (read,read);
        writeln 'resultat = ',!(&(tab)+operation-1); {!! attention, tab va de 1 a 3, mais &(tab) + x pointe sur la x+1 eme case. !!}
      end;
  end
  until operation = 4;
end.
