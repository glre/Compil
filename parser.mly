%{
(* --- préambule: ici du code Caml --- *)
open Ast
open List
%}
/* description des lexèmes */

%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> IDENT
%token <string> CHAINE
%token DPEGAL EGAL DIFFERENT INFEQ SUPEQ INF SUP PLUS MOINS FOIS DIVISE MODULO
%token PARO PARF ACCOLADEO ACCOLADEF CROCHETO CROCHETF VIRGULE PVIRGULE POINT DPOINT PPOINT FORWARD
%token WRITE WRITELN FREE NEW EXIT
%token AND OR NOT TRUE FALSE
%token IF THEN ELSE WHILE DO REPEAT UNTIL FOR TO DOWNTO
%token BEGIN END PROGRAM FUNCTION PROCEDURE
%token TYPE CONST VAR INTEGER BOOLEAN ARRAY STRING REF OF
%token ETCOM BANG READ AROBASE CHAPEAU NULL
%token EOL             /* retour à la ligne */

%nonassoc EGAL INFEQ SUPEQ INF SUP DIFFERENT
%left PLUS MOINS
%left DIVISE FOIS MODULO
%left OR
%left AND
%left NOT

%start main             /* "start" signale le point d'entrée */
%type <Ast.programme> main     /* on _doit_ donner le type du point d'entrée */

%%
    /* --- début des règles de grammaire --- */

main:
  |PROGRAM IDENT liste_parametres PVIRGULE liste_declaration instruction POINT    { DecFonc($2,$3,Entier,$5,$6) }
;


liste_declaration:
  |declaration PVIRGULE liste_declaration                       { $1::$3 }
  |			                                          { [] }
;

declaration:
   VAR IDENT DPOINT genre                                                         { DecVar($2,$4) }
  |CONST IDENT EGAL constante_declaration                                         { DecCons($2,NonSpecifie,$4) }
  |CONST IDENT DPOINT genre EGAL constante_declaration                            { DecCons($2,$4,$6) }
  |PROCEDURE IDENT liste_parametres PVIRGULE liste_declaration instruction           { DecFonc($2,$3,NonSpecifie,$5,$6) }
  |FUNCTION IDENT liste_parametres DPOINT genre PVIRGULE liste_declaration instruction  { DecFonc($2,$3,$5,$7,$8)}
  |PROCEDURE IDENT liste_parametres PVIRGULE FORWARD           							{ DecFonc($2,$3,NonSpecifie,[],Vide) }
  |FUNCTION IDENT liste_parametres DPOINT genre PVIRGULE FORWARD					    { DecFonc($2,$3,$5,[],Vide)}
;

liste_parametres: /*pour gérer le cas de nombre de parametres nul*/
   PARO liste_parametres_non_vide PARF					{$2}
  |							{[]} /*on rejette toto()*/
;

liste_parametres_non_vide:
   parametre PVIRGULE liste_parametres_non_vide                       { $1@$3 }
  |parametre                                                  { $1 }
;

liste_identifiant:
	IDENT			{[$1]}
	|IDENT VIRGULE liste_identifiant {$1::$3}

parametre:
   liste_identifiant DPOINT genre                                        { List.map (fun s -> ParValeur(s,$3)) $1}
  |VAR liste_identifiant DPOINT genre                                    			 { List.map (fun s -> ParAdresse(s,$4)) $2}
;

genre:
   INTEGER                                                                   { Entier }
  |BOOLEAN                                                                   { Booleen }
  |REF OF genre                                                              { Ref $3 }
  |ARRAY CROCHETO liste_intervalle CROCHETF OF genre                               { Tableau($3,$6) }
;

liste_intervalle:
   INT PPOINT INT VIRGULE liste_intervalle                           { ($1,$3)::$5 }
  |INT PPOINT INT                                                            { [$1,$3] }
;

instruction:
   expression DPEGAL expression                               { Affectation($1,$3) }
  |IDENT PARO liste_expression PARF                                          { AppelProc($1,$3) }
  |WRITE liste_expression                                                          { BeginEnd (List.map (fun a -> Write a) $2) }
  |WRITELN liste_expression                                                   { BeginEnd ((List.map (fun a -> Write a) (List.rev (List.tl (List.rev $2))))@[Writeln (List.hd (List.rev $2))])}
  |FREE expression                                                              { Free $2 }
  |EXIT                                                                       { Exit }
  |IF expression DO instruction                                            { Ifte($2,$4,Vide) }
  |IF expression THEN instruction ELSE instruction                           { Ifte($2,$4,$6) }
  |WHILE expression DO instruction                                           { TantQue($2,$4) }
  |REPEAT instruction UNTIL expression                                              { FaitJusquA($2,$4) }
  |FOR IDENT DPEGAL expression TO expression DO instruction                  { Boucle($2,$4,$6,1,$8) }
  |FOR IDENT DPEGAL expression DOWNTO expression DO instruction              { Boucle($2,$4,$6,-1,$8) }
  |BEGIN liste_instruction END						     { BeginEnd $2}
;

liste_instruction:
 instruction PVIRGULE liste_instruction {$1::$3}
|					{[]}

expression:
   NULL                                    { Inttorf (ConsExpr (ConsInt 0)) }
  |AROBASE PARO expression PARF               { Inttorf $3 }
  |CHAPEAU PARO expression PARF               { Rftoint $3 }
  |constante                                { ConsExpr $1 }
  |ETCOM PARO expression PARF               { Adresse $3 }
  |BANG PARO expression PARF                { Dereference $3 }
  |PARO expression PARF                     { $2 }
  |expression PLUS expression               { Plus($1,$3) }
  |expression MOINS expression              { Moins($1,$3) }
  |expression FOIS expression               { Fois($1,$3) }
  |expression DIVISE expression             { Dividende($1,$3) }
  |expression MODULO expression             { Modulo($1,$3) }
  |expression SUPEQ expression              { Supeq($1,$3) }
  |expression SUP expression                { Sup($1,$3) }
  |expression INFEQ expression              { Infeq($1,$3) }
  |expression INF expression                { Inf($1,$3) }
  |expression EGAL expression               { Eq($1,$3) }
  |expression DIFFERENT expression          { Neq($1,$3) }
  |expression AND expression                { Et($1,$3) }
  |expression OR expression                 { Ou($1,$3) }
  |NOT expression                           { Non($2) }
  |IDENT PARO liste_expression PARF         { AppelFonc($1,$3) }
  |IDENT liste_liste_indices                { AccesTabl($1,$2) }
  |READ                                     { Read }
  |NEW PARO expression PARF                           { New $3 }
;

liste_liste_indices:
  | liste_indices liste_liste_indices        { $1::$2 }
  |                                          { [] }
;

liste_indices:
  | CROCHETO liste_expression_non_vide CROCHETF      { $2 }
;

/* Il manque une façon propre pour les appel de fonctions et pour les accès à la table */

liste_expression:
   				{[]}
 |liste_expression_non_vide {$1}

liste_expression_non_vide:
   expression                               { [$1] }
  |expression VIRGULE liste_expression      { $1::$3 }
;

constante:
    MOINS INT                              { ConsInt (-$2) }
  | INT                                    { ConsInt $1 }
  | TRUE                                   { ConsBool true}
  | FALSE                                  { ConsBool false }
  | CHAINE            { ConsString $1 }    
;

constante_declaration:
  | constante { $1 }
  | tableau {$1}
  | IDENT {ConsCons $1}
;


liste_constante:
  | constante_declaration VIRGULE liste_constante      { $1::$3 }
  | constante_declaration                              { [$1] }
;

tableau:
  |PARO liste_constante PARF                { ConsTableau $2 }
;
