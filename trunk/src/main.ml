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

(* Interpreter for EPITA's algorithmic language *)
(* algo.ml: main file                           *)
(*
  Language description and specification by:
  * Christophe Boullay
  * Nathalie Bouquet

  Current version and grammar adaptation by Marwan Burelle.

  Language (original version) description available at
  * http://nathalie.bouquet.free.fr/epita/index.php
*)

let print_type_error s (sp,ep) =
  Format.eprintf "@[<v>Type error: from line %d char %d to line %d char %d@,"
    sp.Lexing.pos_lnum (sp.Lexing.pos_cnum - sp.Lexing.pos_bol)
    ep.Lexing.pos_lnum (ep.Lexing.pos_cnum - ep.Lexing.pos_bol);
  Format.eprintf "%s@]@." s

let tex = ref false
let po  = ref false
let tpo = ref false
let pr  = ref false

let spec =
  [
    ("-tex",Arg.Set tex," pretty-print in LaTeX");
    ("-print-only",Arg.Set po," pretty-print only");
    ("-type-only",Arg.Set tpo," only type validation");
    ("-print", Arg.Set pr, " type validation and pretty-printing")
  ]

let full_pp tex algos td entry_point =
  let (pp_td,pp_algo,pp_main) =
    if tex then
      (Ast.pp_decl_tex,Ast.pp_algo_tex,Ast.pp_entry_point_tex)
    else
      (Ast.pp_decl,Ast.pp_algo,Ast.pp_entry_point)
  in
    begin
      if tex then
	Format.printf "@[<v 2>\\begin{alltt}@,";
      pp_td td;
      Format.printf "@[<v>";
      List.iter (pp_algo) algos;
      pp_main entry_point;
      Format.printf "@]";
      if tex then
	Format.printf "@]@,\\end{alltt}";
      Format.printf "@.";
    end

let file =
object
  val mutable file = ""
  val mutable cin = stdin
  method set f = file <- f; cin <- open_in f
  method get = cin
end

let annon f = file#set f

let main () =
  try
    begin
      Arg.parse (Arg.align spec) annon " Algo's language tools.";
      let cin = file#get
      in
      let lexbuf = Lexing.from_channel cin in
      let ((algos,td), entry_point) = Parser.main Lexer.token lexbuf in
      let (uname,entry_point) = Mangling.mangle_vars_entryp entry_point in
      let static_env = Typing.build_static_env td in
      let builtins = Primitives.builtins () in
      let gl = new T_graphe.graph_loader_primitive in
      let _ =
	begin
	  builtins#add gl#make_builtin;
	end
      in
      let static_env = gl#fusion_senv static_env in
      let (_,_,te) = static_env in
      let fenv = new Typing.funEnv builtins in
	if (not !po) then
	  begin
	    ignore (List.iter (Typing.check_algo static_env fenv) algos);
	    ignore (Typing.check_entry_point static_env fenv entry_point);
	  end;
	if (not (!po || !tpo || !pr)) then
	  begin
	    Format.printf "BEGIN EVALUATION:@.";
	    Memory.eval te algos td entry_point builtins;
	    Format.printf "END EVALUATION@."
	  end;
	if (!po || !pr) then
	  begin
	    let entry_point = Mangling.unmangle_vars_entryp uname entry_point in
	      full_pp (!tex) algos td entry_point;
	  end
    end
  with
      Typing.Type_error (s,l) ->
	print_type_error s l; exit 2
    | Typing.Not_left_value l ->
	print_type_error "expresion is not a left value" l; exit 2

let _ = main ()
