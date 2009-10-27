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

(* ast.ml: abstract syntax tree def and op for algo language *)

(* Type Names *)

type type_name =
    TInt | TBool | TChar | TString | TFloat | TIdent of string

(* expressions *)

type 'loc expr =
    Int   of int * 'loc
  | Float of float * 'loc
  | Bool  of bool * 'loc
  | Char  of char * 'loc
  | Str   of string * 'loc
  | Nul   of 'loc
  | Inf  of 'loc
  | BinOp of string * 'loc expr * 'loc expr * 'loc
  | UniOp of string * 'loc expr * 'loc
  | FCall of string * 'loc expr list * 'loc
  | Ident of string * 'loc
  | Field of 'loc expr * string * 'loc
  | Get   of 'loc expr * 'loc expr list * 'loc

let get_loc = function
    Int (_,l) -> l
  | Float (_,l) -> l
  | Bool (_,l) -> l
  | Char (_,l) -> l
  | Str (_,l) -> l
  | Nul l -> l
  | Inf l -> l
  | BinOp (_,_,_,l) -> l
  | UniOp (_,_,l) -> l
  | FCall (_,_,l) -> l
  | Ident (_,l) -> l
  | Field (_,_,l) -> l
  | Get (_,_,l) -> l

(* instructions *)

type 'loc instr =
    Affect  of 'loc expr * 'loc expr * 'loc
  | PCall   of string * 'loc expr list * 'loc
  | Return  of 'loc expr * 'loc
  | If      of 'loc expr * 'loc instr list * 'loc
  | IfElse  of 'loc expr * 'loc instr list * 'loc instr list * 'loc
  | While   of 'loc expr * 'loc instr list * 'loc
  | DoWhile of 'loc expr * 'loc instr list * 'loc
  | ForUp   of string * 'loc expr * 'loc expr * 'loc instr list * 'loc
  | ForDown of string * 'loc expr * 'loc expr * 'loc instr list * 'loc
  | Switch  of 'loc expr * ('loc expr * ('loc instr list)) list * 'loc

(* Algo *)

type 'loc algo =
    Function of
      string * type_name
      * (type_name * string list * 'loc) list
      * (type_name * string list * 'loc) list
      * (type_name * string list * 'loc) list
      * 'loc instr list
  | Procedure of
      string
      * (type_name * string list * 'loc) list
      * (type_name * string list * 'loc) list
      * (type_name * string list * 'loc) list
      * 'loc instr list

type 'loc entry_point =
    Main of (type_name * string list * 'loc) list * 'loc instr list

(* Types *)
type 'loc type_decl =
    Pointer of type_name * 'loc
  | Array   of 'loc expr list * type_name * 'loc
  | Record  of (type_name * string list * 'loc) list * 'loc

type 'loc decl = {
  constants : (string * 'loc expr * 'loc) list;
  types     : (string * 'loc type_decl * 'loc) list
}

let empty_decl = {
  constants = [] ;
  types = [] ;
}

(* Pretty printing *)

let rec list_printer printer sep = function
    [] -> ()
  | e::[] -> printer e
  | e::t -> (
      printer e;
      Format.printf "%s@;" sep;
      list_printer printer sep t
    )

let rec pp_expr = function
    Int (i,_)         -> Format.printf "%i" i
  | Float (f,_)       -> Format.printf "%f" f
  | Bool (b,_)        ->
      Format.printf "%s"
	(if b then "vrai" else "faux")
  | Char (c,_)        ->
      Format.printf "'%c'" c
  | Str (s,_)         ->
      Format.printf "\"%s\"" s
  | Nul _ ->
      Format.printf "NUL"
  | Inf _ ->
      Format.printf "$"
  | BinOp (o,e1,e2,_) ->
      begin
	Format.printf "(";
	pp_expr e1;
	Format.printf " %s " o;
	pp_expr e2;
	Format.printf ")";
      end
  | UniOp (o,e,_)     ->
      begin
	if (o="^") then
	  begin
	    pp_expr e;
	    Format.printf "^"
	  end
	else
	  begin
	    Format.printf "%s (" o;
	    pp_expr e;
	    Format.printf ")";
	  end
      end
  | FCall (f,el,_)    ->
      begin
	Format.printf "%s(" f;
	list_printer pp_expr "," el;
	Format.printf ")";
      end
  | Ident (i,_)       ->
      Format.printf "%s" i
  | Field (e,f,_)     ->
      begin
	pp_expr e;
	Format.printf ".%s" f
      end
  | Get (t, il, _) ->
      begin
	pp_expr t;
	Format.printf "[";
	list_printer pp_expr "," il;
	Format.printf "]";
      end

let rec pp_instr = function
    Affect (e1,e2,_)     ->
      begin
	Format.printf "@[<h>" ;
	pp_expr e1;
	Format.printf " <- ";
	pp_expr e2;
	Format.printf "@]"
      end
  | PCall (p,el,_)       ->
      begin
	Format.printf "@[<h>%s(" p;
	list_printer pp_expr "," el;
	Format.printf ")@]"
      end
  | Return (e,_)         ->
      begin
	Format.printf "@[<h>retourne (" ;
	pp_expr e;
	Format.printf ")@]"
      end
  | If (c,il,_)          ->
      begin
	Format.printf "@[<v 2>si @[<h>" ;
	pp_expr c;
	Format.printf "@] alors@," ;
	list_printer pp_instr "" il;
	Format.printf "@]@,fin si"
      end
  | IfElse (c,t,e,_)     ->
      begin
	Format.printf "@[<v 2>si @[<h>" ;
	pp_expr c;
	Format.printf "@] alors@," ;
	list_printer pp_instr "" t;
	Format.printf "@]@,@[<v 2>sinon@,";
	list_printer pp_instr "" e;
	Format.printf "@]@,fin si"
      end
  | While (c,il,_)       ->
      begin
	Format.printf "@[<v 2>tant que @[<h>" ;
	pp_expr c;
	Format.printf "@] faire@," ;
	list_printer pp_instr "" il;
	Format.printf "@]@,fin tant que"
      end
  | DoWhile (c,il,_)       ->
      begin
	Format.printf "@[<v 2>faire@," ;
	list_printer pp_instr "" il;
	Format.printf "@]@,@[<h>tantque@;";
	pp_expr c;
	Format.printf "@]";
      end
  | ForUp (i,s,e,il,_)   ->
      begin
	Format.printf "@[<v 2>pour %s <- @[<h>" i;
	pp_expr s;
	Format.printf "@] jusque @[<h>" ;
	pp_expr e;
	Format.printf "@] faire@," ;
	list_printer pp_instr "" il;
	Format.printf "@]@,fin pour"
      end
  | ForDown (i,s,e,il,_) ->
      begin
	Format.printf "@[<v 2>pour %s <- @[<h>" i;
	pp_expr s;
	Format.printf "@] jusque @[<h>" ;
	pp_expr e;
	Format.printf "@] decroissant faire@," ;
	list_printer pp_instr "" il;
	Format.printf "@]@,fin pour"
      end
  | Switch (e, sl, _)    ->
      begin
	Format.printf "@[<v 2>selon @[<h>";
	pp_expr e;
	Format.printf "@] faire@," ;
	list_printer
	  (function (e,il) ->
	     pp_expr e;
	     Format.printf ":@[<v>";
	     list_printer pp_instr "" il;
	     Format.printf "@]@,"
	  ) "" sl;
	Format.printf "@]@,fin selon"
      end

let pp_typename = function
    TInt -> "entier"
  | TBool -> "booleen"
  | TChar -> "charactere"
  | TString -> "chaine"
  | TFloat -> "reel"
  | TIdent id -> id

let pp_algo = function
    Function (f,tn,pl,pg,v,il) ->
      begin
	Format.printf "@,@[<v 2>Algorithme Fonction %s : %s" f (pp_typename tn);
	if pl <> [] then
	  begin
	    Format.printf "@,@[<v 2>Parametres Locaux";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pl;
	    Format.printf "@]";
	  end;
	if pg <> [] then
	  begin
	    Format.printf "@,@[<v 2>Parametres Globaux@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pg;
	    Format.printf "@]";
	  end;
	if v <> [] then
	  begin
	    Format.printf "@,@[<v 2>Variables";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	    Format.printf "@]";
	  end;
	Format.printf "@]@,@[<v 2>Debut@,";
	list_printer pp_instr "" il;
	Format.printf "@]@,Fin Algorithme Fonction %s@," f
      end
  | Procedure (f,pl,pg,v,il) ->
      begin
	Format.printf "@,@[<v 2>Algorithme Procedure %s@," f;
	if pl <> [] then
	  begin
	    Format.printf "@[<v 2>Parametres Locaux";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pl;
	    Format.printf "@]@,";
	  end;
	if pg <> [] then
	  begin
	    Format.printf "@[<v 2>Parametres Globaux@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pg;
	    Format.printf "@]@,";
	  end;
	Format.printf "@[<v 2>Variables";
	if v <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	  end;
	Format.printf "@]@]@,@[<v 2>Debut@,";
	list_printer pp_instr "" il;
	Format.printf "@]@,Fin Algorithme Procedure %s@," f
      end

let pp_entry_point = function
    Main (v,il) ->
      begin
	Format.printf "@,@[<v 2>";
	Format.printf "@[<v 2>Variables";
	if v <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	  end;
	Format.printf "@]@]@,@[<v 2>Debut@,";
	list_printer pp_instr "" il;
	Format.printf "@]@,Fin@,"
      end

let pp_type_decl n = function
    Pointer (tn,_) -> Format.printf "@[<h>%s =@;^%s@]@," n (pp_typename tn)
  | Array (el,tn,_) -> 
      begin
	Format.printf "@[<h>%s =@;" n;
	list_printer pp_expr " *" el;
	Format.printf " %s@]@," (pp_typename tn)
      end
  | Record (fl,_) ->
      begin
	Format.printf "@[<v 2>%s = enregistrement" n;
	if fl <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" fl;
	  end;
	Format.printf "@]@,fin enregistrement@,";
      end

let pp_constants cl =
  begin
    Format.printf "@[<v 2>constantes@;";
    list_printer
      (
	function (n,e,_) ->
	  Format.printf "@[<h>%s =@;" n;
	  pp_expr e;
	  Format.printf "@]@,";
      ) "" cl;
    Format.printf "@]@,";
  end

let pp_decl d =
  begin
    if d.constants <> [] then
      pp_constants d.constants;
    if d.types <> [] then
      begin
	Format.printf "@[<v 2>types@,";
	list_printer (fun (n,t,_) -> pp_type_decl n t) "" d.types ;
	Format.printf "@]@,";
      end
  end

(* PP LaTeX *)

let rec pp_expr_tex = function
    Int (i,_)         -> Format.printf "%i" i
  | Float (f,_)       -> Format.printf "%f" f
  | Bool (b,_)        ->
      Format.printf "%s"
	(if b then "vrai" else "faux")
  | Char (c,_)        ->
      Format.printf "'%c'" c
  | Str (s,_)         ->
      Format.printf "\"%s\"" s
  | Nul _ ->
      Format.printf "\\nul"
  | Inf _ ->
      Format.printf "\\(\\infty\\)"
  | BinOp (o,e1,e2,_) ->
      let o = match o with
	  "et"|"ou" -> "\\"^o
	| _ -> o
      in
	begin
	  Format.printf "(";
	  pp_expr_tex e1;
	  Format.printf " %s " o;
	  pp_expr_tex e2;
	  Format.printf ")";
	end
  | UniOp (o,e,_)     ->
      let o = match o with
	  "non" -> "\\"^o
	| _ -> o
      in
	begin
	  if (o="^") then
	    begin
	      pp_expr_tex e;
	      Format.printf "\\T{}"
	    end
	  else
	    begin
	      Format.printf "%s " o;
	      pp_expr_tex e;
	    end
	end
  | FCall (f,el,_)    ->
      begin
	Format.printf "@[<h 2>%s(" f;
	list_printer pp_expr_tex "," el;
	Format.printf ")@]";
      end
  | Ident (i,_)       ->
      Format.printf "%s" i
  | Field (e,f,_)     ->
      begin
	pp_expr_tex e;
	Format.printf ".%s" f
      end
  | Get (t, il, _) ->
      begin
	pp_expr_tex t;
	Format.printf "@[<h 2>[";
	list_printer pp_expr_tex "," il;
	Format.printf "]@]";
      end

let rec pp_instr_tex = function
    Affect (e1,e2,_)     ->
      begin
	Format.printf "@[<h>" ;
	pp_expr_tex e1;
	Format.printf " \\aff ";
	pp_expr_tex e2;
	Format.printf "@]"
      end
  | PCall (p,el,_)       ->
      begin
	Format.printf "@[<h>%s(" p;
	list_printer pp_expr_tex "," el;
	Format.printf ")@]"
      end
  | Return (e,_)         ->
      begin
	Format.printf "@[<h>retourne (" ;
	pp_expr_tex e;
	Format.printf ")@]"
      end
  | If (c,il,_)          ->
      begin
	Format.printf "@[<v 2>\\si " ;
	pp_expr_tex c;
	Format.printf " \\alors@," ;
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\si"
      end
  | IfElse (c,t,e,_)     ->
      begin
	Format.printf "@[<v 2>\\si " ;
	pp_expr_tex c;
	Format.printf " \\alors@," ;
	list_printer pp_instr_tex "" t;
	Format.printf "@]@,@[<v 2>\\sinon@,";
	list_printer pp_instr_tex "" e;
	Format.printf "@]@,\\fin \\si"
      end
  | While (c,il,_)       ->
      begin
	Format.printf "@[<v 2>\\tantque " ;
	pp_expr_tex c;
	Format.printf " \\faire@," ;
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\tantque"
      end
  | DoWhile (c,il,_)       ->
      begin
	Format.printf "@[<v 2>\\faire@," ;
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,@[<h>\\tantque@;";
	pp_expr_tex c;
	Format.printf "@]";
      end
  | ForUp (i,s,e,il,_)   ->
      begin
	Format.printf "@[<v 2>\\pour %s \\aff " i;
	pp_expr_tex s;
	Format.printf " \\jusqua " ;
	pp_expr_tex e;
	Format.printf " \\faire@," ;
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\pour"
      end
  | ForDown (i,s,e,il,_) ->
      begin
	Format.printf "@[<v 2>\\pour %s <- " i;
	pp_expr_tex s;
	Format.printf " \\jusqua " ;
	pp_expr_tex e;
	Format.printf " \\decroissant \\faire@," ;
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\pour"
      end
  | Switch (e, sl, _)    ->
      begin
	Format.printf "@[<v 2>\\selon ";
	pp_expr_tex e;
	Format.printf " \\faire@," ;
	list_printer
	  (function (e,il) ->
	     pp_expr_tex e;
	     Format.printf ":@[<v>";
	     list_printer pp_instr_tex "" il;
	     Format.printf "@]@,"
	  ) "" sl;
	Format.printf "@]@,\\finselon"
      end

let pp_algo_tex = function
    Function (f,tn,pl,pg,v,il) ->
      begin
	Format.printf "@,@[<v 2>\\algorithme \\fonction %s : %s" f (pp_typename tn);
	if pl <> [] then
	  begin
	    Format.printf "@,@[<v 2>\\parametres \\locaux";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pl;
	    Format.printf "@]";
	  end;
	if pg <> [] then
	  begin
	    Format.printf "@,@[<v 2>\\parametres \\globaux@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pg;
	    Format.printf "@]";
	  end;
	if v <> [] then
	  begin
	    Format.printf "@,@[<v 2>\\variables";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	    Format.printf "@]";
	  end;
	Format.printf "@]@,@[<v 2>\\debut@,";
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\algorithme \\fonction %s@," f
      end
  | Procedure (f,pl,pg,v,il) ->
      begin
	Format.printf "@,@[<v 2>\\algorithme \\procedure %s@," f;
	if pl <> [] then
	  begin
	    Format.printf "@[<v 2>\\parametres \\locaux";
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pl;
	    Format.printf "@]@,";
	  end;
	if pg <> [] then
	  begin
	    Format.printf "@[<v 2>\\parametres \\globaux@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" pg;
	    Format.printf "@]@,";
	  end;
	Format.printf "@[<v 2>\\variables";
	if v <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	  end;
	Format.printf "@]@]@,@[<v 2>\\debut@,";
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin \\algorithme \\procedure %s@," f
      end

let pp_entry_point_tex = function
    Main (v,il) ->
      begin
	Format.printf "@,@[<v 2>";
	Format.printf "@[<v 2>\\variables";
	if v <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" v;
	  end;
	Format.printf "@]@]@,@[<v 2>\\debut@,";
	list_printer pp_instr_tex "" il;
	Format.printf "@]@,\\fin@,"
      end


let pp_type_decl_tex n = function
    Pointer (tn,_) -> Format.printf "@[<h>%s =@;\\T{}%s@]@," n (pp_typename tn)
  | Array (el,tn,_) -> 
      begin
	Format.printf "@[<h>%s =@;" n;
	list_printer pp_expr_tex " *" el;
	Format.printf " %s@]@," (pp_typename tn)
      end
  | Record (fl,_) ->
      begin
	Format.printf "@[<v 2>%s = \\enregistrement" n;
	if fl <> [] then
	  begin
	    Format.printf "@,";
	    list_printer
	      (function (t,vl,_) ->
		 Format.printf "@[<h>%s\t" (pp_typename t);
		 list_printer (Format.printf "%s") ", " vl;
		 Format.printf "@]"
	      )
	      "" fl;
	  end;
	Format.printf "@]@,\\fin \\enregistrement@,";
      end

let pp_constants_tex cl =
  begin
    Format.printf "@[<v 2>\\constantes@;";
    list_printer
      (
	function (n,e,_) ->
	  Format.printf "@[<h>%s =@;" n;
	  pp_expr_tex e;
	  Format.printf "@]@,";
      ) "" cl;
    Format.printf "@]@,";
  end

let pp_decl_tex d =
  begin
    if d.constants <> [] then
      pp_constants_tex d.constants;
    if d.types <> [] then
      begin
	Format.printf "@[<v 2>\\types@,";
	list_printer (fun (n,t,_) -> pp_type_decl_tex n t) "" d.types ;
	Format.printf "@]@,";
      end
  end
