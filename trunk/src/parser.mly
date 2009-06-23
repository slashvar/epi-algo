%{
(* Copyright (c) 2009, Marwan BURELLE                                 *)
(* All rights reserved.                                               *)

(* Redistribution and use in source and binary forms, with or without *)
(* modification, are permitted provided that the following conditions *)
(* are met:                                                           *)

(* * Redistributions of source code must retain the above copyright   *)
(*   notice, this list of conditions and the following disclaimer.    *)
(* * Redistributions in binary form must reproduce the above          *)
(*   copyright notice, this list of conditions and the following      *)
(*   disclaimer in the documentation and/or other materials provided  *)
(*   with the distribution.                                           *)
(* * Neither the name of the Marwan Burelle nor the names of its      *)
(*   contributors may be used to endorse or promote products derived  *)
(*   from this software without specific prior written permission.    *)

(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND             *)
(* CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,        *)
(* INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF           *)
(* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE           *)
(* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS *)
(* BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,           *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED    *)
(* TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,      *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON  *)
(* ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR *)
(* TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF *)
(* THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(* SUCH DAMAGE.                                                       *)

  (* parser.mly: YACC grammar*)

  open Lexing
  open Parsing

  exception Error_algo_close of string * position * position * position

  let get_pos i = (rhs_start_pos i, rhs_end_pos i)
  let make_pos () = (symbol_start_pos (),symbol_end_pos ())

  let make_type = function
      "entier" -> Ast.TInt
    | "reel" -> Ast.TFloat
    | "booleen" -> Ast.TBool
    | "caractere" -> Ast.TChar
    | "chaine" -> Ast.TString
    | s -> Ast.TIdent s

  let print_error () =
    let (sp,ep) = make_pos () in
      Printf.printf "Syntax error: from line %d char %d to line %d char %d\n"
	sp.pos_lnum (sp.pos_cnum - sp.pos_bol)
	ep.pos_lnum (ep.pos_cnum - ep.pos_bol);
      exit 3

%}

%token <int> INT
%token <bool> BOOL
%token <float> FLOAT
%token <char> CHAR
%token <string> STR
%token <string> ID
%token NUL
%token CTE RECORD TYPES
%token ADD MIN MUL DIV SLASH MOD INF
%token REF ARROW DOT RETURN DP
%token LE LT GT GE EQ NEQ NOT AND OR
%token IF THEN ELSE FOR TO DESC WHILE SO WHILESO SWITCH DO END
%token ALGO FUNCTION PROCEDURE START PARAM LOCAL GLOBAL VAR
%token LPAREN RPAREN LBRACE RBRACE COMMA
%token EOL
%token EOF
%right NOT
%left OR AND
%left LE GE LT GT EQ NEQ
%left MOD
%left ADD MIN
%left MUL DIV SLASH
%nonassoc UMINUS
%nonassoc LBRACE
%right REF
%left DOT
%start main             /* the entry point */
%start only_decl
%type <(((Lexing.position * Lexing.position) Ast.algo) list * (Lexing.position * Lexing.position) Ast.decl) * (Lexing.position * Lexing.position) Ast.entry_point > main
%type < (Lexing.position * Lexing.position) Ast.decl > only_decl
%%

  main:
| glob_decl entry_point { ($1,$2) } ;

  entry_point:
| var START EOL blcode END { Ast.Main ($1,$4) }

  glob_decl:
| algo_list {
    ($1,Ast.empty_decl)
  }
| cte_decl algo_list {
    ($2, { Ast.empty_decl with Ast.constants = $1 } )
  }
| types algo_list {
    ($2, { Ast.empty_decl with Ast.types = $1 } )
  }
|  cte_decl types algo_list {
    let d = { Ast.constants = $1;
	      Ast.types = $2;
	    } in
      ($3,d)
  }
      ;

  only_decl:
|  cte_decl types
      {
	let d =
	  {
	    Ast.constants = $1;
	    Ast.types = $2;
	  }
	in d
      }
| types
      {
	let d =
	  {
	    Ast.empty_decl with Ast.types = $1
	  }
	in d
      }
  ;

  algo_list:
| algo { $1::[] }
| algo algo_list { $1::$2 }
  ;

  algo:
| ALGO FUNCTION ID DP ID EOL proto START EOL blcode END ALGO FUNCTION ID EOL {
    if $3 = $14 then
      let (pl,pg,var) = $7 in
	Ast.Function($3, make_type $5, pl, pg, var, $10)
    else
      raise (Error_algo_close($14,symbol_start_pos(),rhs_start_pos 14,rhs_end_pos 14))
  }
| ALGO PROCEDURE ID EOL proto START EOL blcode END ALGO PROCEDURE ID EOL {
    if $3 = $12 then
      let (pl,pg,var) = $5 in
	Ast.Procedure($3, pl, pg, var, $8)
    else
      raise (Error_algo_close($12,symbol_start_pos(),rhs_start_pos 12,rhs_end_pos 12))
  }
| error { print_error () }
  ;

  proto:
| pl pg var { ($1,$2,$3) }
| pl var    { ($1,[],$2) }
| pg var    { ([],$1,$2) }
| pl pg	    { ($1,$2,[]) }
| pl        { ($1,[],[]) }
| pg        { ([],$1,[]) }
| var       { ([],[],$1) }
|           { ([],[],[]) }
  ;

  cte_decl:
    CTE EOL cdeclist { $3 }
  ;

  cdeclist:
    cdecl cdeclist1 { $1::$2 }
| {[]}
  ;

  cdeclist1:
    EOL cdecl cdeclist1 { $2::$3 }
| EOL cdeclist1 { $2 }
| EOL { [] }
  ;

  cdecl:
    ID EQ expr { ($1,$3,make_pos ()) } ;

  types:
    TYPES EOL tlist { $3 }
  ;
  tlist:
| tdecl tlist1 { $1::$2 }
| EOL tlist { $2 }
| { [] }
  ;
  tlist1:
    EOL tdecl tlist1 { $2::$3 }
| EOL tlist1 { $2 }
| EOL { [] }
  ;

  tdecl:
    ID EQ texpr { ($1,$3, make_pos ()) } ;

  texpr:
    REF ID { Ast.Pointer ( make_type $2, get_pos 2) }
| record { $1 }
| array_decl { $1 }
  ;

  array_decl:
    dimlist ID { Ast.Array ($1, make_type $2, make_pos ())}
;

  dimlist:
  expr { [$1] }
| expr MUL dimlist { $1::$3 }
;

  record:
    RECORD EOL varlist END RECORD {
      Ast.Record ($3,make_pos ())
    }
  ;

  pl:
| PARAM LOCAL EOL varlist { $4 }
  ;

  pg:
| PARAM GLOBAL EOL varlist { $4 }
  ;

  var:
| VAR EOL varlist { $3 }
  ;

  varlist:
    varlist1 { $1 }
| ID idlist varlist1 { (make_type $1, $2, get_pos 1)::$3 }
| { [] }
;
  varlist1:
    EOL ID idlist varlist1 { (make_type $2, $3, get_pos 1)::$4 }
| EOL varlist1 { $2 }
| EOL { [] }

  idlist:
    ID { $1::[] }
| ID COMMA idlist { $1::$3 }
  ;

  blcode:
| instr blcode1 { $1::$2 }
  ;

  blcode1:
| EOL blcode1 { $2 }
| EOL { [] }
| EOL instr blcode1 { $2::$3}
;

  instr:
    lexpr ARROW expr { Ast.Affect ($1,$3,make_pos ()) }
| ID LPAREN exprlist RPAREN
      { Ast.PCall ($1,$3,make_pos ()) }
| RETURN expr { Ast.Return ($2, make_pos ()) }
| IF expr THEN EOL blcode END IF
      { Ast.If ($2,$5,make_pos ()) }
| IF expr THEN EOL blcode ELSE EOL blcode END IF
      { Ast.IfElse ($2,$5,$8,make_pos ()) }
| DO EOL blcode WHILESO expr
      { Ast.DoWhile ($5,$3,make_pos ()) }
| WHILE SO expr DO EOL blcode END WHILE SO
      { Ast.While ($3,$6,make_pos ()) }
| FOR ID ARROW expr TO expr DO EOL blcode END FOR
      { Ast.ForUp ($2,$4,$6,$9,make_pos ()) }
| FOR ID ARROW expr TO expr DESC DO EOL blcode END FOR
      { Ast.ForDown ($2,$4,$6,$10,make_pos ()) }
| SWITCH expr DO EOL swbloc END SWITCH
      { Ast.Switch ($2,$5,make_pos ()) }
  ;

  lexpr:
    ID { Ast.Ident ($1,make_pos ()) }
| lexpr DOT ID { Ast.Field ($1,$3,make_pos ()) }
| lexpr REF { Ast.UniOp ("^",$1,make_pos ()) }
| lexpr LBRACE exprlist RBRACE { Ast.Get ($1,$3, make_pos()) }
| LPAREN lexpr RPAREN { $2 }
;

  exprlist:
    expr exprlist1 {$1::$2}
| { [] }
;
  exprlist1:
    COMMA expr exprlist1 { $2::$3 }
| { [] }
;

  swbloc:
    expr DP blcode { ($1,$3)::[] }
| expr DP blcode swbloc { ($1,$3)::$4 }
  ;

  expr:
| NUL { Ast.Nul (make_pos ()) }
| INF {Ast.Inf (make_pos ()) }
| INT { Ast.Int ($1,make_pos ()) }
| BOOL { Ast.Bool ($1,make_pos ()) }
| FLOAT { Ast.Float ($1,make_pos ()) }
| CHAR { Ast.Char ($1,make_pos ()) }
| STR { Ast.Str ($1,make_pos ()) }
| ID { Ast.Ident ($1,make_pos ()) }
| LPAREN expr RPAREN { $2 }
| expr ADD expr { Ast.BinOp ("+",$1,$3,make_pos ()) }
| expr MIN expr { Ast.BinOp ("-",$1,$3,make_pos ()) }
| expr MUL expr { Ast.BinOp ("*",$1,$3,make_pos ()) }
| expr DIV expr { Ast.BinOp ("div",$1,$3,make_pos ()) }
| expr SLASH expr { Ast.BinOp ("/",$1,$3,make_pos ()) }
| expr MOD expr { Ast.BinOp ("%",$1,$3,make_pos ()) }
| expr LT expr { Ast.BinOp ("<",$1,$3,make_pos ()) }
| expr LE expr { Ast.BinOp ("<=",$1,$3,make_pos ()) }
| expr GT expr { Ast.BinOp (">",$1,$3,make_pos ()) }
| expr GE expr { Ast.BinOp (">=",$1,$3,make_pos ()) }
| expr EQ expr { Ast.BinOp ("=",$1,$3,make_pos ()) }
| expr NEQ expr { Ast.BinOp ("<>",$1,$3,make_pos ()) }
| expr AND expr { Ast.BinOp ("et",$1,$3,make_pos ()) }
| expr OR expr { Ast.BinOp ("ou",$1,$3,make_pos ()) }
| NOT expr { Ast.UniOp ("non",$2,make_pos ()) }
| MIN expr %prec UMINUS { Ast.UniOp ("-",$2,make_pos ()) }
| ID LPAREN exprlist RPAREN { Ast.FCall ($1,$3,make_pos ()) }
| expr REF { Ast.UniOp ("^",$1,make_pos ()) }
| expr DOT ID { Ast.Field ($1,$3,make_pos ()) }
| expr LBRACE exprlist RBRACE { Ast.Get ($1,$3, make_pos()) }
  ;
