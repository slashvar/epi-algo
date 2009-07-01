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

(* t_graphe.ml: Concrete graph data structures support                *)

open Native_data

(* inner representation of dynamic graph in target language *)
let t_graphe_d =
  "types
  t_listsom = ^s_som
  t_listadj = ^s_adj

  s_som = enregistrement
    entier	som
    t_listadj	succ,pred
    t_listsom	suiv
  fin enregistrement

  s_adj = enregistrement
    entier	nbliens
    reel	cout
    t_listsom	vsom
    t_listadj	suiv
  fin enregistrement

  t_graphe_d = enregistrement
    entier	ordre
    booleen	orient
    t_listsom	lsom
  fin enregistrement
"

let t_graphe_d_ast = Parser.only_decl Lexer.token (Lexing.from_string t_graphe_d)

let t_graphe_d_env = Typing.build_static_env t_graphe_d_ast

let (tGrapheD,tListSom,tListAdj,sSom,sAdj) = match t_graphe_d_env with
    (_,_,te) ->
      (
	te#make_real_type (Ast.TIdent "t_graphe_d"),
	te#make_real_type (Ast.TIdent "t_listsom"),
	te#make_real_type (Ast.TIdent "t_listadj"),
	te#make_real_type (Ast.TIdent "s_som"),
	te#make_real_type (Ast.TIdent "s_adj")
      )

class t_graph_d cc =
object (s)
  inherit target_graph tGrapheD cc as super
  method init orient ord =
    begin
      super#init orient ord;
      for i = 1 to ord do
	let p = cc#get_mem#alloc in
	let ps = Memory.Pointer p in
	  cc#get_mem#set p (cc#get_cs#get_init#build_value sSom);
	  Memory.get_field_set "som" (cc#get_mem#get p) (Memory.Int i);
	  Memory.get_field_set "suiv" (cc#get_mem#get p)
	    (Memory.get_field "lsom" g);
	  Memory.get_field_set "lsom" g ps;
      done;
    end
  method find_vertice id =
    let unmatch_id p =
      (Memory.get_int (Memory.get_field "som" (Memory.deref cc#get_mem p)))<>id
    in
    let ps = ref (Memory.get_field "lsom" g) in
      while (!ps <> Memory.Nul && (unmatch_id !ps)) do
	ps := Memory.get_field "suiv" (Memory.deref cc#get_mem !ps)
      done; !ps

  method private new_edge cost nblink target next =
    let p = cc#get_mem#alloc in
      cc#get_mem#set p (cc#get_cs#get_init#build_value sAdj);
      set_fields_p cc p [
	("nbliens", Memory.Int nblink);
	("cout", Memory.Float cost);
	("vsom", target);
	("suiv", next)
      ];
      Memory.Pointer p

  method add_edge src dst cost nblink =
    let ps = s#find_vertice src in
    let tg = s#find_vertice dst in
    let pa = s#new_edge cost nblink tg (get_field cc ps "succ") in
	set_fields cc ps [("succ",pa)];
	if (Memory.get_bool (Memory.get_field "orient" g)) then
	  let ppa = s#new_edge cost nblink ps (get_field cc tg "pred") in
	    set_fields cc tg [("pred",ppa)]
end

(* inner representation of static graph in target language *)
let t_graphe_s =
  "constantes
  MAX_SOMMETS = 100

types
  t_mat_adj =  MAX_SOMMETS * MAX_SOMMETS entier
  t_mat_cout = MAX_SOMMETS * MAX_SOMMETS reel

  t_graphe_s = enregistrement
    entier	ordre
    booleen	orient
    t_mat_adj	adj
    t_mat_cout	cout
  fin enregistrement
"

let t_graphe_s_ast = Parser.only_decl Lexer.token (Lexing.from_string t_graphe_s)

let t_graphe_s_env = Typing.build_static_env t_graphe_s_ast

let tGrapheS = match t_graphe_s_env with
    (_,_,te) ->
      te#make_real_type (Ast.TIdent "t_graphe_s")

class t_graph_s cc =
object (s)
  inherit target_graph tGrapheS cc as super
  method init orient ord =
    begin
      super#init orient ord;
      let adj = Memory.get_field "adj" g in
      let cout = Memory.get_field "cout" g in
	for i = 1 to ord do
	  for j = 1 to ord do
	    matrix_set adj  (i-1) (j-1) (Memory.Int 0);
	    matrix_set cout (i-1) (j-1) (Memory.Float 0.);
	  done
	done;
    end

  method add_edge src dst cost nblink =
    let adj = Memory.get_field "adj" g in
    let cout = Memory.get_field "cout" g in
      matrix_set adj  (src-1) (dst-1) (Memory.Int nblink);
      matrix_set cout (src-1) (dst-1) (Memory.Float cost);
      if not (Memory.get_bool (Memory.get_field "orient" g)) then
	begin
	  matrix_set adj  (src-1) (dst-1) (Memory.Int nblink);
	  matrix_set cout (dst-1) (src-1) (Memory.Float cost);
	end
end

let graph_senv = Typing.static_env_fusion t_graphe_s_env t_graphe_d_env

class graph_factory cc file =
  let lexIn =
    Genlex.make_lexer kw (Stream.of_channel (open_in file))
  in
  let (ori, od, el) =
    parse_graph lexIn
  in
  let g = new graph ori od in
object (s)
  val igraph = g

  method make_dynamic =
    let tg = new t_graph_d cc in
      igraph#export (tg:>target_graph);
      tg

  method make_static =
    let tg = new t_graph_s cc in
      igraph#export (tg:>target_graph);
      tg

  initializer
    List.iter
      (fun (src,dst,cost,nblink) -> g#add_edges src dst cost nblink)
      el
end

class ['tc,'cc] graph_loader_primitive =
object (s:'s)
  constraint 'tc = (Lexing.position * Lexing.position) Typing.typing_ctx
  constraint 'cc =
    ((Lexing.position * Lexing.position), Memory.memory) Memory.callctx

  val mutable file = ""

  method set_file (cc:'cc) (tc:'tc) =
      file <- (match cc#get_arg with
		   Some (Memory.Str f) -> f
		 | _ -> assert false);
      Memory.Nul

  method make_graph (cc:'cc) (tc:'tc) =
    try
      let factory = new graph_factory cc file in
      let dyn =
	match tc#get_type with
	  | Typing.Tname n ->
	      n = "t_graphe_d"
	  | _ -> assert false
      in
      let g =
	if dyn then
	  begin
	    factory#make_dynamic#get_value
	  end
	else
	  begin
	    factory#make_static#get_value
	  end
      in
      let (_, set) = cc#glob_arg in
	set g; Memory.Nul
    with
	Invalid_argument _ ->
	  begin
	    Printf.fprintf stderr "make_graph gl\n";
	    exit 3
	  end

  method typechk (tc:'tc) =
    try
      begin
	match tc#get_type with
	  | Typing.TString when tc#get_rank = 0 -> Typing.TString
	  | Typing.Tname ("t_graphe_d" | "t_graphe_s")
	      when tc#get_rank = 1 && tc#is_left_value ->
	      Typing.Pointer Typing.TVoid
	  | t when tc#get_rank = 0 ->
	      raise (Typing.Type_mismatch (t,Typing.TString))
	  | t when tc#get_rank = 1 ->
	      raise (Typing.Type_mismatch (t,Typing.Tname "t_graphe_?"))
	  | _ -> raise Typing.Too_many_parameters
      end
    with
	Invalid_argument _ ->
	  begin
	    Printf.fprintf stderr "typechk gl\n";
	    exit 3
	  end

  method make_builtin =
    let b =
      new Builtins.builtin_var_overload
	"charger_graphe"
	s#typechk
    in
      begin
	b#build_variadic [
	  (Typing.TString,            s#set_file);
	  (Typing.Tname "t_graphe_d", s#make_graph);
	  (Typing.Tname "t_graphe_s", s#make_graph);
	];
	(b :
	   (((Lexing.position * Lexing.position), Memory.memory)
	      Memory.callctx,
            (Lexing.position * Lexing.position) Typing.typing_ctx,
            (Lexing.position * Lexing.position), Memory.value,
	    Typing.ctype, Typing.ctype) Builtins.builtin_var_overload
	 :>
	   (((Lexing.position * Lexing.position), Memory.memory)
	      Memory.callctx,
            (Lexing.position * Lexing.position) Typing.typing_ctx,
            (Lexing.position * Lexing.position), Memory.value,
	    Typing.ctype) Builtins.builtin)
      end

  method fusion_senv se = Typing.static_env_fusion se graph_senv
  method get_static_env d = Typing.extend_static_env graph_senv d

end
