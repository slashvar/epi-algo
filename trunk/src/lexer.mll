{

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

(* lexer.mll: lexing for algo language *)

  open Parser
  open Lexing
  exception Error_lex of string * position * position

  let update_lexbuf lexbuf =
    let p = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <- {
	p with
	  pos_lnum = p.pos_lnum + 1;
	  pos_bol  = p.pos_cnum;
      }

  let update_nlexbuf n lexbuf =
    for i = 1 to n do
      update_lexbuf lexbuf
    done

  let ht_kwd = Hashtbl.create 53
  let kwd = [ ("tant",		WHILE);
	      ("tantque",	WHILESO);
	      ("que",		SO);
	      ("pour",		FOR);
	      ("jusque",	TO);
	      ("faire",		DO);
	      ("fin",		END);
	      ("Fin",		END);
	      ("si",		IF);
	      ("sinon",		ELSE);
	      ("alors",		THEN);
	      ("descroissant",	DESC);
	      ("retourne",	RETURN);
	      ("algorithme",	ALGO);
	      ("Algorithme",	ALGO);
	      ("fonction",	FUNCTION);
	      ("Fonction",	FUNCTION);
	      ("procedure",	PROCEDURE);
	      ("Procedure",	PROCEDURE);
	      ("parametres",	PARAM);
	      ("Parametres",	PARAM);
	      ("locaux",	LOCAL);
	      ("Locaux",	LOCAL);
	      ("local",		LOCAL);
	      ("Local",		LOCAL);
	      ("global",	GLOBAL);
	      ("Global",	GLOBAL);
	      ("globaux",	GLOBAL);
	      ("Globaux",	GLOBAL);
	      ("Variables",	VAR);
	      ("debut",		START);
	      ("Debut",		START);
	      ("selon",		SWITCH);
	      ("et",		AND);
	      ("ou",		OR);
	      ("non",		NOT);
	      ("vrai",		BOOL(true));
	      ("faux",		BOOL(false));
	      ("NUL",		NUL);
	      ("div",		DIV);
	      ("constantes",	CTE);
	      ("Constantes",	CTE);
	      ("types",		TYPES);
	      ("Types",		TYPES);
	      ("enregistrement",RECORD);
	    ]
  let _ = List.iter (function (k,v) -> Hashtbl.add ht_kwd k v) kwd

  let ht_sym = Hashtbl.create 17
  let sym =
    [ ("+",	ADD);
      ("-",	MIN);
      ("*",	MUL);
      ("/",	SLASH);
      ("%",	MOD);
      ("^",	REF);
      ("<-",	ARROW);
      (".",	DOT);
      (":",	DP);
      (">",	GT);
      (">=",	GE);
      ("<",	LT);
      ("<=",	LE);
      ("<>",	NEQ);
      ("=",	EQ);
      (",",	COMMA);
      ("(",	LPAREN);
      (")",	RPAREN);
      ("[",	LBRACE);
      ("]",	RBRACE);
      ("$",     INF);
    ]
  let _ = List.iter (function (k,v) -> Hashtbl.add ht_sym k v) sym

}

let ident = ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*
let symba = "+" | "-" | "*" | "/" | "%" | "^" | "<-" | "." | ":" | ">" | ">=" | "<" | "<=" | "<>" | "=" | "," | "(" | ")" | "[" | "]" | "$"

rule token = parse
    (*consume space and empty line *)
    [' ' '\t']				{ token lexbuf }
  | ['\n']+ as lxm			{ update_nlexbuf (String.length lxm) lexbuf; EOL }
  | eof					{ EOF }
  | "/*"				{ comment lexbuf }
  | ['0'-'9']+ as lxm			{ INT(int_of_string lxm) }
  | ['0'-'9']+'.'['0'-'9']+ as lxm	{ FLOAT(float_of_string lxm) }
  | "'"(_ as c)"'"			{ CHAR(c) }
  | '"'([^'"']* as s)'"'		{ STR(s) }
  | ident as i				{ try
					    Hashtbl.find ht_kwd i
					  with
					      Not_found -> ID(i)
					}
  |  symba as s				{ try
					    Hashtbl.find ht_sym s
					  with
					      Not_found -> raise
						(Error_lex (s,
							    lexeme_start_p lexbuf,
							    lexeme_end_p lexbuf))
					}
and comment = parse
    "*/"				{ token lexbuf }
  | ['\n']				{ update_lexbuf lexbuf; comment lexbuf }
  | _					{ comment lexbuf }
