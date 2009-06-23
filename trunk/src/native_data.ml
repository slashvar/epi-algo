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

(* native_data.ml: Native data structures support *)

(* Graph representations: we have 2 classical kind of graphs that can
    be used. Our purpose is to offer generic graph loading and
    auto-fill of either kind of graph. *)

(* First, we define graph internaly *)

type edges =
{
  dst    : int;
  cost   : float;
  nblink : int;
}

type vertex =
{
  id           : int;
  mutable succ : edges list;
  mutable pred : edges list;
}

(* simple parser for loading *)
let kw = ["ordre"; ":"; "->"; "("; ")"; "oriente"; "non"; "{"; "}"; ";"; ","]

let parse_edge =
  parser
    | [< 'Genlex.Int src ; 'Genlex.Kwd "->"; 'Genlex.Kwd("(");
	 'Genlex.Int dst; 'Genlex.Kwd ","; (cost,nblink) =
	  (parser
	       [< 'Genlex.Int nblink; 'Genlex.Kwd ")"; >] ->
		 (0.,nblink)
	     | [< 'Genlex.Float cost;
		  'Genlex.Kwd ","; 'Genlex.Int nblink; 'Genlex.Kwd ")"
	       >] -> (cost,nblink)
	  );
	 'Genlex.Kwd ";" >] -> (src,dst,cost,nblink)

let rec parse_edges_list =
  parser
    | [< e = parse_edge; l = parse_edges_list; >] -> e::l
    | [< >] -> []

let parse_graph =
  parser
      [< 'Genlex.Kwd "{";
	 orient = (parser
		       [< 'Genlex.Kwd "oriente">] -> true
		     | [< 'Genlex.Kwd "non"; 'Genlex.Kwd "oriente">] -> false
		  );
	 'Genlex.Kwd ";";
	 'Genlex.Kwd "ordre"; 'Genlex.Kwd ":"; 'Genlex.Int od;
	 'Genlex.Kwd ";";
	 el = parse_edges_list;
	 'Genlex.Kwd "}" >] -> (orient,od,el)

(* Helpers for value manipulations *)

let set_field cc f p v =
  Memory.get_field_set f (cc#get_mem#get p) v

let rec set_fields_p cc p = function
    [] -> ()
  | (f,v)::t ->
      begin
	set_field cc f p v;
	set_fields_p cc p t;
      end

let set_fields cc p l = match p with
    Memory.Pointer p -> set_fields_p cc p l
  | _ -> assert false

let get_field cc ps n =
  Memory.get_field n (Memory.deref cc#get_mem ps)

let matrix_set m x y v =
  let row = match m with
      Memory.Array a -> a.(x)
    | _ -> assert false
  in
    match row with
	Memory.Array a -> a.(y) <- v
      | _ -> assert false

let matrix_get m x y =
  let row = match m with
      Memory.Array a -> a.(x)
    | _ -> assert false
  in
    match row with
	Memory.Array a -> a.(y)
      | _ -> assert false

class virtual target_graph tgraph cc =
object (s)
  val mutable g = Memory.Nul
  method init orient ord =
    begin
      g <- cc#get_cs#get_init#build_value tgraph;
      Memory.get_field_set "ordre" g (Memory.Int ord);
      Memory.get_field_set "orient" g (Memory.Bool orient);
    end
  method virtual add_edge : int -> int -> float -> int -> unit
  method get_value = g
end

class ['dg] graph orient ord =
object (s)
  constraint 'dg = #target_graph
  val orient:bool = orient
  val order:int   = ord
  val vertices =
    Array.init ord (fun x -> {id = x+1; succ = []; pred = []})

  method add_edges src dst cost nblink =
    try
      begin
	vertices.(src-1).succ <-
	  {dst=dst;cost=cost;nblink=nblink}::vertices.(src-1).succ;
	if (orient) then
	  vertices.(dst-1).pred <-
	  {dst=src;cost=cost;nblink=nblink}::vertices.(dst-1).pred
	else
	  vertices.(dst-1).succ <-
	    {dst=src;cost=cost;nblink=nblink}::vertices.(dst-1).succ
      end
    with
	Invalid_argument _ ->
	  begin
	    Printf.fprintf stderr "add_edges\n";
	    exit 3
	  end

  method export (ig:'dg) =
    begin
      try
	ig#init orient ord ;
	Array.iter
	  (fun v -> List.iter
	     (fun e -> ig#add_edge v.id e.dst e.cost e.nblink)
	     v.succ
	  ) vertices;
      with
	  Invalid_argument _ ->
	    begin
	      Printf.fprintf stderr "graph export\n";
	      exit 3
	    end
    end

  method pp =
    begin
      Format.printf "{@[<v 2>@,";
      if orient then
	Format.printf "oriente;@,"
      else
	Format.printf "non oriente;@,";
      Format.printf "ordre: %i;" order;
      Array.iter
	(
	  fun v ->
	    List.iter
	      (
		fun e ->
		  if (orient || e.dst > v.id) then
		    Format.printf "@,%i -> (%i,%F,%i);"
		      v.id e.dst e.cost e.nblink
	      ) v.succ
	) vertices;
      Format.printf "@]@,}@."
    end

end

let load_graph file =
  let lexIn =
    Genlex.make_lexer kw (Stream.of_channel (open_in file))
  in
  let (ori, od, el) =
    parse_graph lexIn
  in
  let g = new graph ori od in
    begin
      List.iter
	(fun (src,dst,cost,nblink) -> g#add_edges src dst cost nblink)
	el;
      g
    end
