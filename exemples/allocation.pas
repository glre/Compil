program main;
var i: ref of integer;
var j: ref of integer;
var k: ref of integer;
begin
  i := new(5);
  writeln 'j ai alloue 5 dans i : ',i;
  j := new(5);
  writeln 'j ai alloue 5 dans j : ',j;
  k := new(5);
  writeln 'j ai alloue 5 dans k : ',k,'\n';
  writeln 'je libere j';
  free(j);
  writeln 'je libere i\n';
  free(i);
  i := new(13);
  writeln 'j ai alloue 13 dans i : ',i;
  writeln 'i a ete alloue dans l espace libere\n';
  free(i);
  i := new(13);
  writeln 'je relibere i et je realloue 13, i vaut toujours ',i,'\n';
  free(i);
  i := new(14);
  writeln 'je relibere i et je realloue 14, i vaut cette-fois ci ',i,'\n';
  free(i);
  i := new(5);
  writeln 'apres liberation de i, j ai realloue 5 dans i, et i vaut ',i,' comme au debut';
  j := new(5);
  writeln 'j ai realloue aussi 5 dans j, et j vaut ',j,' comme au debut\n';
  writeln 'je libere i,j,k dans l ordre i k j\n';
  free(i);
  free(k);
  free(j);
  i:= new(42);
  writeln 'l allocation de 42 dans i montre que le tas est revenu comme au debut; i vaut ',i,'\n';
end.

