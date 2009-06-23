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

(* mangling.ml: uniform renaming variables *)

class uniq_name prefix =
object (s)
  val mutable cpt = 0
  val env = Hashtbl.create 53
  val uenv = Hashtbl.create 53
  method add v =
    begin
      cpt <- cpt+1;
      Hashtbl.add env v (prefix ^ v ^ (string_of_int cpt));
      Hashtbl.add uenv (prefix ^ v ^ (string_of_int cpt)) v;
    end
  method name v =
    try
      Hashtbl.find env v
    with
	Not_found -> v
  method uname v =
    try
      Hashtbl.find uenv v
    with
	Not_found -> v
end

let rec mangle_vars_expr u = function
  | ( Ast.Int (_,_) | Ast.Float (_,_) | Ast.Bool (_,_) | Ast.Char (_,_)
    | Ast.Str (_,_) | Ast.Nul _ | Ast.Inf _) as e -> e
  | Ast.BinOp(o,e1,e2,l) ->
      Ast.BinOp(o, mangle_vars_expr u e1, mangle_vars_expr u e2,l)
  | Ast.UniOp(o,e1,l) ->
      Ast.UniOp(o, mangle_vars_expr u e1,l)
  | Ast.FCall(f,el,l) ->
      Ast.FCall(f,List.map (mangle_vars_expr u) el,l)
  | Ast.Ident (v,l) ->
      Ast.Ident (u#name v,l)
  | Ast.Field (e,f,l) ->
      Ast.Field (mangle_vars_expr u e,f,l)
  | Ast.Get (e,el,l) ->
      Ast.Get (mangle_vars_expr u e, List.map (mangle_vars_expr u) el,l)

let rec mangle_vars_instr u = function
  | Ast.Affect (e1,e2,l) ->
      Ast.Affect (mangle_vars_expr u e1,mangle_vars_expr u e2,l)
  | Ast.PCall (p,el,l) ->
      Ast.PCall (p, List.map (mangle_vars_expr u) el,l)
  | Ast.Return (e,l) ->
      Ast.Return (mangle_vars_expr u e,l)
  | Ast.If (c,el,l) ->
      Ast.If (mangle_vars_expr u c, List.map (mangle_vars_instr u) el, l)
  | Ast.IfElse (c,el1,el2,l) ->
      Ast.IfElse (mangle_vars_expr u c,
		  List.map (mangle_vars_instr u) el1,
		  List.map (mangle_vars_instr u) el2,l)
  | Ast.While (c, el, l) ->
      Ast.While (mangle_vars_expr u c, List.map (mangle_vars_instr u) el, l)
  | Ast.DoWhile (c, el, l) ->
      Ast.DoWhile (mangle_vars_expr u c, List.map (mangle_vars_instr u) el, l)
  | Ast.ForUp (v,e1, e2, il, l) ->
      Ast.ForUp (u#name v, mangle_vars_expr u e1, mangle_vars_expr u e2,
		 List.map (mangle_vars_instr u) il,l)
  | Ast.ForDown (v,e1, e2, il, l) ->
      Ast.ForDown (u#name v, mangle_vars_expr u e1, mangle_vars_expr u e2,
		   List.map (mangle_vars_instr u) il,l)
  | Ast.Switch (e,sl,l) ->
      Ast.Switch (mangle_vars_expr u e,
		  List.map (fun (e,il) -> (mangle_vars_expr u e,
					   List.map (mangle_vars_instr
						       u) il)) sl, l)

let rec unmangle_vars_expr u = function
  | ( Ast.Int (_,_) | Ast.Float (_,_) | Ast.Bool (_,_) | Ast.Char (_,_)
    | Ast.Str (_,_) | Ast.Nul _ | Ast.Inf _) as e -> e
  | Ast.BinOp(o,e1,e2,l) ->
      Ast.BinOp(o, unmangle_vars_expr u e1, unmangle_vars_expr u e2,l)
  | Ast.UniOp(o,e1,l) ->
      Ast.UniOp(o, unmangle_vars_expr u e1,l)
  | Ast.FCall(f,el,l) ->
      Ast.FCall(f,List.map (unmangle_vars_expr u) el,l)
  | Ast.Ident (v,l) ->
      Ast.Ident (u#uname v,l)
  | Ast.Field (e,f,l) ->
      Ast.Field (unmangle_vars_expr u e,f,l)
  | Ast.Get (e,el,l) ->
      Ast.Get (unmangle_vars_expr u e, List.map (unmangle_vars_expr u) el,l)

let rec unmangle_vars_instr u = function
  | Ast.Affect (e1,e2,l) ->
      Ast.Affect (unmangle_vars_expr u e1,unmangle_vars_expr u e2,l)
  | Ast.PCall (p,el,l) ->
      Ast.PCall (p, List.map (unmangle_vars_expr u) el,l)
  | Ast.Return (e,l) ->
      Ast.Return (unmangle_vars_expr u e,l)
  | Ast.If (c,el,l) ->
      Ast.If (unmangle_vars_expr u c, List.map (unmangle_vars_instr u) el, l)
  | Ast.IfElse (c,el1,el2,l) ->
      Ast.IfElse (unmangle_vars_expr u c,
		  List.map (unmangle_vars_instr u) el1,
		  List.map (unmangle_vars_instr u) el2,l)
  | Ast.While (c, el, l) ->
      Ast.While (unmangle_vars_expr u c, List.map (unmangle_vars_instr u) el, l)
  | Ast.DoWhile (c, el, l) ->
      Ast.DoWhile (unmangle_vars_expr u c, List.map (unmangle_vars_instr u) el, l)
  | Ast.ForUp (v,e1, e2, il, l) ->
      Ast.ForUp (u#uname v, unmangle_vars_expr u e1, unmangle_vars_expr u e2,
		 List.map (unmangle_vars_instr u) il,l)
  | Ast.ForDown (v,e1, e2, il, l) ->
      Ast.ForDown (u#uname v, unmangle_vars_expr u e1, unmangle_vars_expr u e2,
		   List.map (unmangle_vars_instr u) il,l)
  | Ast.Switch (e,sl,l) ->
      Ast.Switch (unmangle_vars_expr u e,
		  List.map (fun (e,il) -> (unmangle_vars_expr u e,
					   List.map (unmangle_vars_instr
						       u) il)) sl, l)

let mangle_vars_entryp = function
    Ast.Main (vars,il) ->
      begin
	let u = new uniq_name "global_" in
	let mvars =
	  List.map (
	    function (t,vl,l) ->
	      (t,
	       List.map (fun v -> u#add v ; u#name v) vl,
	       l)
	  ) vars
	in
	  (u,Ast.Main(mvars, List.map (mangle_vars_instr u) il))
      end

let unmangle_vars_entryp u = function
    Ast.Main (vars,il) ->
      begin
	let mvars =
	  List.map (
	    function (t,vl,l) ->
	      (t,
	       List.map (fun v -> u#uname v) vl,
	       l)
	  ) vars
	in
	  Ast.Main(mvars, List.map (unmangle_vars_instr u) il)
      end
