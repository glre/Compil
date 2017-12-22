{
open Parser;;        (* le type "token" est défini dans parser.mli *)
exception Eof;;
let caractere = ref 0;;
let ligne = ref 0;;
}

let chiffre = ['0'-'9']
let nombre = chiffre+ | chiffre+
let lettre = ['a'-'z'] | ['A'-'Z'] | '_'
let ident = lettre (lettre | chiffre)*
let chaine = '\'' [^'\'']* '\''
let commentaire = '{' [^'}']* '}'
let commentaire2 = "\"" [^'"']* "\""

rule token = parse
  | [' ' '\t']     { incr caractere; token lexbuf }
  | commentaire     { token lexbuf }
  | commentaire2     { token lexbuf }
  | '\n'            { caractere := 0;incr ligne; token lexbuf}
  | nombre as k { INT (int_of_string k) }
  | ":="            { caractere := !caractere + 2; DPEGAL }
  | '='             { incr caractere; EGAL }
  | "<="            { caractere := !caractere + 2;INFEQ }
  | ">="            { caractere := !caractere + 2;SUPEQ }
  | '<'             { incr caractere; INF }
  | '>'             { incr caractere; SUP }
  | "<>"            { caractere := !caractere + 2; DIFFERENT }
  | "mod"           { caractere := !caractere + 3; MODULO }
  | "null"          { caractere := !caractere + 4; NULL }

  | '+'             { incr caractere; PLUS }
  | '-'             { incr caractere; MOINS }
  | '*'             { incr caractere; FOIS }
  | '/'             { incr caractere; DIVISE }

  | '('             { incr caractere; PARO }
  | ')'             { incr caractere; PARF }
  | '{'             { incr caractere; ACCOLADEO }
  | '}'             { incr caractere; ACCOLADEF }
  | '['             { incr caractere; CROCHETO }
  | ']'             { incr caractere; CROCHETF }
  | ','             { incr caractere; VIRGULE }
  | ';'             { incr caractere; PVIRGULE }
  | ".."            { caractere := !caractere + 2; PPOINT }
  | '.'             { incr caractere; POINT }
  | ':'             { incr caractere; DPOINT }

  | '@'             { incr caractere; AROBASE }
  | '^'             { incr caractere; CHAPEAU }

  | "and"           { caractere := !caractere + 3; AND }
  | "or"            { caractere := !caractere + 2; OR }
  | "not"           { caractere := !caractere + 3; NOT }

  | "if"            { caractere := !caractere + 2; IF }
  | "then"          { caractere := !caractere + 4; THEN }
  | "else"          { caractere := !caractere + 5; ELSE }

  | "while"         { caractere := !caractere + 5; WHILE }
  | "do"            { caractere := !caractere + 2; DO }
  | "repeat"        { caractere := !caractere + 6; REPEAT }
  | "until"         { caractere := !caractere + 5; UNTIL }
  | "for"           { caractere := !caractere + 3; FOR }
  | "to"            { caractere := !caractere + 2; TO }
  | "downto"        { caractere := !caractere + 6; DOWNTO }
  | "new"           { caractere := !caractere + 3; NEW }
  | "free"           { caractere := !caractere + 4; FREE }
  | "exit"          { caractere := !caractere + 4; EXIT }
  | "begin"         { caractere := !caractere + 5; BEGIN }
  | "end"           { caractere := !caractere + 3; END }
  | "program"       { caractere := !caractere + 7; PROGRAM }
  | "function"      { caractere := !caractere + 8; FUNCTION }
  | "procedure"     { caractere := !caractere + 9; PROCEDURE }

  | "type"          { caractere := !caractere + 4; TYPE }
  | "const"         { caractere := !caractere + 5; CONST }
  | "var"           { caractere := !caractere + 3; VAR }
  | "integer"       { caractere := !caractere + 7; INTEGER }
  | "boolean"       { caractere := !caractere + 7; BOOLEAN }
  | "array"         { caractere := !caractere + 5; ARRAY }
  | "string"        { caractere := !caractere + 6; STRING }
  | "forward"       { caractere := !caractere + 7; FORWARD }
  | "write"         { caractere := !caractere + 5; WRITE }
  | "writeln"         { caractere := !caractere + 7; WRITELN }

  | "of"            { caractere := !caractere + 2; OF }

  | "ref"           { caractere := !caractere +3; REF }
  | "&"             {incr caractere; ETCOM }
  | "!"             {incr caractere; BANG }
  | "read"          { READ }

  | "true"          { caractere := !caractere + 4; TRUE }
  | "false"         { caractere := !caractere + 5; FALSE }
  | ident as k      { caractere := !caractere + String.length k; IDENT k }
  | chaine as c     { let l = String.length c in CHAINE (String.sub c 1 (l-2))}
  | eof             { raise Eof } 
