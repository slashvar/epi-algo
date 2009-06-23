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

(* memory.ml: Memory model and evaluation rules for algo language     *)

type value =
  | Nul
  | Int of int
  | Char of char
  | Bool of bool
  | Float of float
  | Inf
  | Str of string
  | Pointer of int
  | Record of (string,value) Hashtbl.t
  | Array of value array

exception Segfault of int
exception Nul_pointer

let rec val_eq v1 v2 = match (v1,v2) with
    (Nul, Nul)
  | (Nul, Pointer 0) | (Pointer 0, Nul)
  | (Inf,Inf) -> true
  | (Int i1, Int i2) -> i1=i2
  | (Char i1, Char i2) -> i1=i2
  | (Bool i1, Bool i2) -> i1=i2
  | (Float i1, Float i2) -> i1=i2
  | (Str i1, Str i2) -> i1=i2
  | (Pointer i1, Pointer i2) -> i1=i2
  | (Record h1, Record h2) -> h1 = h2
  | (Array a1, Array a2) -> a1 = a2
  | _ -> false


let backchar = Hashtbl.create 17
let backcharl = ["\\n";"\\t"]
let _ = List.iter (function (k,v) -> Hashtbl.add backchar k v)
  [
    "\\n", "\n";
    "\\t", "\t"
  ]
let rg = Str.regexp (String.concat "\\|" (List.map Str.quote backcharl))
let normStr s =
  Str.global_substitute rg
    (fun x -> Hashtbl.find backchar (Str.matched_string  x)) s

let rec value2str = function
    Nul -> "NUL"
  | Int i -> string_of_int i
  | Char c -> String.make 1 c
  | Bool b -> if b then "VRAI" else "FAUX"
  | Float f -> string_of_float f
  | Inf -> "infini"
  | Str s -> normStr s
  | Pointer p -> "$"^(string_of_int p)
  | Record h ->
      "{ "^
	(Hashtbl.fold (fun k v s -> s^k^" = "^(value2str v)^"; ") h "")
      ^"}"
  | Array _ ->
      "[| TABLEAUX |]"

class memory =
object (s)
  val mutable size = 0
  val mem = Hashtbl.create 53
  method newp = size <- size + 1 ; size
  method alloc =
    Hashtbl.add mem s#newp Nul; size
  method free p =
    Hashtbl.remove mem p
  method get p =
    if p = 0 then raise Nul_pointer;
    try Hashtbl.find mem p with
	Not_found -> raise (Segfault p)
  method set p v =
    if p = 0 then raise Nul_pointer;
    if Hashtbl.mem mem p then
      begin
	Hashtbl.replace mem p v
      end
    else raise Nul_pointer
end

class init_value (te:Typing.type_env) =
object (s)

  method build_value t = match te#real_type t with
      Typing.Record h -> s#build_record h
    | Typing.Array (d,dl,t) -> s#build_array (d,dl,t)
    | _ -> Nul

  method build_record h =
    let hv = Hashtbl.create (Hashtbl.length h) in
      Hashtbl.iter (fun f t -> Hashtbl.add hv f (s#build_value t)) h;
      Record hv

  method build_array = function
      (1,d1::[],t) ->
	Array (Array.init d1 (fun _ -> s#build_value t))
    | (d,d1::dl,t) ->
	Array (Array.init d1 (fun _ -> s#build_array (d-1,dl,t)))
    | _ -> assert false

  method get_type_env = te

end

class call_stack (iv:init_value) =
object (s)
  val global = Hashtbl.create 7
  val local  = Hashtbl.create 7
  val vars   = Hashtbl.create 13
  val init_v = iv

  method get_init = init_v
  method add_global (x:string) set get =
    Hashtbl.add global x (set,get)
  method add_local x v =
    Hashtbl.add local x v
  method add_vars x t =
    Hashtbl.add vars x (init_v#build_value t)

  method get_global x =
    (snd (Hashtbl.find global x))()

  method get x =
    try Hashtbl.find vars x with
	Not_found ->
	  begin
	    try Hashtbl.find local x with
		Not_found -> s#get_global x
	  end

  method set_global x v =
    (fst (Hashtbl.find global x)) v

  method set x v =
    if Hashtbl.mem vars x then
      Hashtbl.replace vars x v
    else
      if Hashtbl.mem local x then
	Hashtbl.replace local x v
      else
	s#set_global x v

  method make_global x =
    ((fun () -> s#get x), s#set x)

  method remove_global v =
    Hashtbl.remove global v
  method remove_local v =
    Hashtbl.remove local v
  method remove_vars v =
    Hashtbl.remove vars v

end

let get_field f = function
    Record fields -> Hashtbl.find fields f
  | _ -> assert false

let get_int = function
    Int i -> i
  | _ -> assert false

let get_bool = function
    Bool b -> b
  | _ -> assert false

let get_index i = function
    Array tab -> tab.(get_int i)
  | _ -> assert false

let deref (mem:memory) = function
    Pointer i -> mem#get i
  | _ -> assert false

let get_field_set f = function
    Record fields -> Hashtbl.replace fields f
  | _ -> assert false

let get_index_set i = function
    Array tab -> (fun v -> tab.(get_int i) <- v)
  | _ -> assert false

let deref_set (mem:memory) = function
    Pointer p -> mem#set p
  | _ -> assert false

exception Invalid_operation

let op_eval mem cs o p = match (o,p) with
    ("+",[Int i1; Int i2]) -> Int (i1+i2)
  | ("-",[Int i1; Int i2]) -> Int (i1-i2)
  | ("*",[Int i1; Int i2]) -> Int (i1*i2)
  | ("/",[Int i1; Int i2]) -> Int (i1/i2)
  | ("%",[Int i1; Int i2]) -> Int (i1 mod i2)
  | ("div",[Int i1; Int i2]) -> Int (i1/i2)
  | ("+.",[Float i1; Float i2]) -> Float (i1+.i2)
  | ("-",[Float i1; Float i2]) -> Float (i1-.i2)
  | ("*.",[Float i1; Float i2]) -> Float (i1*.i2)
  | ("/.",[Float i1; Float i2]) -> Float (i1/.i2)
  | ("+",[Str s1; Str s2]) -> Str (s1^s2)
  | ("-",[Int i]) -> Int (-i)
  | ("-",[Float i]) -> Float (-.i)
  | ("non",[Bool b]) -> Bool (not b)
  | ("et",[Bool b1; Bool b2]) -> Bool (b1 && b2)
  | ("<",[v1;v2]) -> Bool (v1<v2)
  | ("<=",[v1;v2]) -> Bool (v1<=v2)
  | (">",[v1;v2]) -> Bool (v1>v2)
  | (">=",[v1;v2]) -> Bool (v1>=v2)
  | ("=",[v1;v2]) -> Bool (v1=v2)
  | ("<>",[v1;v2]) -> Bool (v1<>v2)
  | ("^",[p]) -> deref mem p
  | ("f2i",[Float f]) -> Int (int_of_float f)
  | ("i2f",[Int i]) -> Float (float i)
  | (_,(Nul::_|_::Nul::_)) -> raise (Nul_pointer)
  | _ -> raise (Invalid_operation)

let rec eval_expr fenv mem cs = function
    Ast.Int (i,_) -> Int i
  | Ast.Float (i,_) -> Float i
  | Ast.Char (i,_) -> Char i
  | Ast.Bool (i,_) -> Bool i
  | Ast.Inf _ -> Inf
  | Ast.Str (i,_) -> Str i
  | Ast.Nul _ -> Nul
  | Ast.BinOp ("et",e1,e2,_) ->
      Bool ((get_bool (eval_expr fenv mem cs e1))
	    &&
	    (get_bool (eval_expr fenv mem cs e2)))
  | Ast.BinOp ("ou",e1,e2,_) ->
      Bool ((get_bool (eval_expr fenv mem cs e1))
	    ||
	    (get_bool (eval_expr fenv mem cs e2)))
  | Ast.BinOp (op,e1,e2,_) ->
      op_eval mem cs op
	[(eval_expr fenv mem cs e1);(eval_expr fenv mem cs e2)]
  | Ast.UniOp(op,e,_) ->
      op_eval mem cs op [eval_expr fenv mem cs e]
  | Ast.FCall (f,el,l) ->
      fenv#call f el mem cs l
  | Ast.Ident (x,_) -> cs#get x
  | Ast.Field (e,f,_) ->
      get_field f (eval_expr fenv mem cs e)
  | Ast.Get (e,el,_) ->
      List.fold_left
	(fun a i -> get_index i a)
	(eval_expr fenv mem cs e)
	(List.map (eval_expr fenv mem cs) el)

let left_eval fenv mem cs = function
    Ast.Ident (x,_) ->
      cs#set x
  | Ast.UniOp ("^",e,_) ->
      deref_set mem (eval_expr fenv mem cs e)
  | Ast.Field (e,f,_) ->
      get_field_set f (eval_expr fenv mem cs e)
  | Ast.Get (e,el,_) ->
      let rec aux a = function
	  [] -> assert false
	| h::[] -> get_index_set (eval_expr fenv mem cs h) a
	| h::t ->
	    aux (get_index (eval_expr fenv mem cs h) a) t
      in aux (eval_expr fenv mem cs e) el
  | _ -> assert false

let glob_eval fenv mem cs = function
    Ast.Ident (x,_) ->
      cs#make_global x
  | Ast.UniOp ("^",e,_) ->
      let v = (eval_expr fenv mem cs e) in
	((fun () -> deref mem v), deref_set mem v)
  | Ast.Field (e,f,_) ->
      let v = (eval_expr fenv mem cs e) in
	((fun () -> get_field f v), get_field_set f v)
  | Ast.Get (e,el,_) ->
      let rec aux a = function
	  [] -> assert false
	| h::[] ->
	    let v = (eval_expr fenv mem cs h) in
	      ((fun () -> get_index v a), get_index_set v a)
	| h::t ->
	    aux (get_index (eval_expr fenv mem cs h) a) t
      in aux (eval_expr fenv mem cs e) el
  | e ->
      begin
	Format.printf "Glob_eval: @[<v>";
	Ast.pp_expr e;
	Format.printf "@]@.";
	exit 4;
      end

let make_incr x l =
  Ast.Affect (
    Ast.Ident (x,l),
    Ast.BinOp ("+", Ast.Ident (x,l), Ast.Int (1,l),l),
    l
  )

let make_decr x l =
  Ast.Affect (
    Ast.Ident (x,l),
    Ast.BinOp ("-", Ast.Ident (x,l), Ast.Int (1,l),l),
    l
  )

let rec eval_block ret fenv mem cs il =
  List.for_all (eval_instr ret fenv mem cs) il
and eval_instr ret fenv mem cs = function
    Ast.Affect (le,re,_) ->
     (left_eval fenv mem cs le (eval_expr fenv mem cs re); true)
  | Ast.Return (e,_) ->
      (ret := eval_expr fenv mem cs e; false)
  | Ast.If(c,il,_) ->
      if (get_bool (eval_expr fenv mem cs c)) then
	eval_block ret fenv mem cs il
      else true
  | Ast.IfElse (c,il1,il2,_) ->
      if get_bool (eval_expr fenv mem cs c) then
	eval_block ret fenv mem cs il1
      else
	eval_block ret fenv mem cs il2
  | Ast.While (c,il,_) as i ->
      if (get_bool (eval_expr fenv mem cs c)) then
	(eval_block ret fenv mem cs il)
	&& eval_instr ret fenv mem cs i
      else true
  | Ast.DoWhile (c,il,_) as i ->
      (eval_block ret fenv mem cs il)
      && (
	if (get_bool (eval_expr fenv mem cs c)) then
	  eval_instr ret fenv mem cs i
	else true
      )
  | Ast.ForUp (x,se,ee,il,l) ->
      eval_block ret fenv mem cs
	[
	  Ast.Affect (Ast.Ident (x,l),se,l);
	  Ast.While (
	    Ast.BinOp ("<=",Ast.Ident (x,l),ee,l),
	    il@[(make_incr x l)],l
	  );
	]
  | Ast.ForDown (x,se,ee,il,l) ->
      eval_block ret fenv mem cs
	[
	  Ast.Affect (Ast.Ident (x,l),se,l);
	  Ast.While (
	    Ast.BinOp (">=",Ast.Ident (x,l),ee,l),
	    il@[(make_decr x l)],l
	  );
	]
  | Ast.PCall (f,el,l) ->
      (ignore (fenv#call f el mem cs l); true)
  | Ast.Switch (e,swb,_) ->
      let v = eval_expr fenv mem cs e in
	try
	  let (_,il) =
	    List.find
	      (fun (e,_) -> val_eq v (eval_expr fenv mem cs e))
	      swb
	  in
	    eval_block ret fenv mem cs il
	with
	    Not_found -> assert false
  | _ -> assert false

class ['loc,'mem] callctx (el: 'loc Ast.expr list) fenv (mem:'mem) (cs:call_stack) l =
object (s:'self)
  constraint 'mem = #memory

  val loc:'loc = l
  val arguments = Array.of_list el
  val mutable index = 0

  method get_loc = loc

  method get_rank = index

  method next_arg =
    begin
      if (index < (Array.length arguments) - 2 ) then
	(index <- index + 1; Some index)
      else
	(index <- index + 1; None)
    end

  method get_exprarg =
    try
      Some (arguments.(index))
    with
	Invalid_argument _ -> None

  method glob_arg =
    let a = match s#get_exprarg with
	None -> assert false
      | Some a -> a
    in
      glob_eval fenv mem cs a

  method get_arg =
    try
      Some (eval_expr fenv mem cs arguments.(index))
    with
	Invalid_argument _ -> None

  method arg_count = Array.length arguments

  method reset = index <- -1

  method iter_call (call: 'self -> value) =
    match s#next_arg with
	None -> call s
      | _ -> ignore (call s); s#iter_call call

  method get_mem = mem
  method get_cs = cs

end

type fun_param = Local of string | Global of string
type 'loc fun_bloc  =
    {
      param : fun_param list;
      vars  : (string * Typing.ctype) list;
      code  : 'loc Ast.instr list;
    }

class ['a,'b] function_env (b:'b) (iv:init_value)=
object (s)

  val env = Hashtbl.create 29
  val builtins = b
  val mutable cpt = 0

  method private nextcpt = cpt <- cpt + 1; string_of_int cpt

  method add (f : 'a Ast.algo) =
    match f with
	Ast.Function(name,_,local,global,vars,il)
      | Ast.Procedure(name,local,global,vars,il)
	->
	  Hashtbl.add env name (
	    {
	      code  = il;
	      vars  =
		List.fold_left
		  (fun l (tn,v,_) ->
		     List.rev_append
		       (iv#get_type_env#build_var_list (tn,v)) l) [] vars;
	      param =
		let rec build_param local global =
		  match (local,global) with
		      ([],[]) -> []
		    | ([],(a,[],b)::g) ->
			build_param [] g
		    | ([],(a,h::t,b)::g) ->
			Global h :: build_param [] ((a,t,b)::g)
		    | ((a,[],b)::l,_) ->
			build_param l global
		    | ((a,h::t,b)::l,_) ->
			Local h :: build_param ((a,t,b)::l) global
		in
		  build_param local global
	    }
	  )

  method call name (el: 'a Ast.expr list) mem (cs:call_stack) l =
    try
      s#inner_call (Hashtbl.find env name) el mem cs
    with
	Not_found -> s#builtin_call name el mem cs l

  method private inner_call f (el: 'a Ast.expr list) mem (cs:call_stack) =
    let u = new Mangling.uniq_name ("pg_"^s#nextcpt) in
    let ret = ref Nul in
      begin
	List.iter2 (
	  fun e -> function
	      Local x  -> cs#add_local x (eval_expr s mem cs e)
	    | Global x ->
		let (get,set) = glob_eval s mem cs e in
		  begin
		    u#add x;
		    cs#add_global (u#name x) set get;
		  end
	) el f.param;
	let code = List.map (Mangling.mangle_vars_instr u) f.code in
          List.iter (fun (v,t) -> cs#add_vars v t) f.vars;
	  ignore (eval_block ret s mem cs code);
	  List.iter
	    (function
		 Local v  -> cs#remove_local v
	       | Global v -> cs#remove_global (u#name v)) f.param;
	  List.iter (function (v,_) -> cs#remove_vars v) f.vars;
	  !ret;
      end

  method private builtin_call name el mem cs (l:'a) =
    builtins#call name (new callctx el s mem cs l)

end

(* Global full eval *)

let eval te algos td (Ast.Main (v,il)) builtins =
  let iv = new init_value te in
  let cs = new call_stack iv in
  let mem = new memory in
  let fenv = new function_env builtins iv in
  let ret = ref Nul in
  let vars =
    List.fold_left
      (fun l (tn,v,_) ->
	 List.rev_append (iv#get_type_env#build_var_list (tn,v)) l) [] v
  in
    begin
      List.iter
	(fun (n,e,_) -> cs#add_local n (eval_expr fenv mem cs e))
	td.Ast.constants;
      List.iter fenv#add algos;
      List.iter (fun (v,t) -> cs#add_vars v t) vars;
      try ignore (eval_block ret fenv mem cs il)
      with
	  Typing.Type_unknown n ->
	    begin
	      Printf.fprintf stderr "Unknown type: %s\n" n;
	      exit 3
	    end
	| Invalid_argument _ ->
	    begin
	      Printf.fprintf stderr "in eval\n";
	      exit 3
	    end
    end
