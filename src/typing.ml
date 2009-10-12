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

(* typing.ml: Typing for EPITA's algo language *)

module Env = Map.Make (String)
module TypeSet = Set.Make (String)

(* Gestion des constantes *)

type cte =
    Int of int
  | Float of float
  | Bool of bool
  | Char of char
  | Str of string

exception Not_cte of (Lexing.position * Lexing.position)
exception Wrong_cte of (Lexing.position * Lexing.position)

let is_cte cte_env = function
    Ast.Int (v,_) -> true
  | Ast.Float (v,_) -> true
  | Ast.Bool (v,_) -> true
  | Ast.Char (v,_) -> true
  | Ast.Str (v,_) -> true
  | Ast.Ident (x,_) ->
      Env.mem x cte_env
  | _ -> false

let eval_cte cte_env = function
    Ast.Int (v,_) -> Int v
  | Ast.Float (v,_) -> Float v
  | Ast.Bool (v,_) -> Bool v
  | Ast.Char (v,_) -> Char v
  | Ast.Str (v,_) -> Str v
  | Ast.Ident (x,l) ->
      begin
	try
	  Env.find x cte_env
	with
	    Not_found -> raise (Not_cte l)
      end
  | e -> raise (Not_cte (Ast.get_loc e))

let rec eval_cexpr f = function
    [] -> (0,[])
  | h::t ->
      let (n,lv) = eval_cexpr f t in
	(n+1,f h::lv)

let get_int cte_env e =
  match eval_cte cte_env e with
      Int v -> v
    | _ -> raise (Wrong_cte (Ast.get_loc e))

let make_cte_env l env =
  List.fold_left
    (fun env (n,e,_) -> Env.add n (eval_cte env e) env)
    env l


(* Checking type names existance *)

exception Type_unknown of string

let build_type_name_set l =
  List.fold_left
    (fun s (n,_,_) -> TypeSet.add n s) TypeSet.empty l

(* Concrete type representation *)

type ctype =
    TInt | TBool | TChar | TString | TFloat
  | TVoid
  | Tname of string
  | Pointer of ctype
  | Array of int * int list * ctype
  | Record of (string,ctype) Hashtbl.t

let rec ctype2str = function
    TInt | TBool | TChar | TString | TFloat -> "base type"
  | TVoid -> "void"
  | Tname s -> s
  | Pointer t -> "^"^ctype2str t
  | Array (_,d1::dl,t) ->
      (List.fold_left
	 (fun s d -> s ^ " * " ^ (string_of_int d))
	 (string_of_int d1) dl)
      ^ (ctype2str t)
  | Record _ -> "record"
  | _ -> assert false

let type_cte = function
  | Int   _ -> TInt
  | Float _ -> TFloat
  | Bool  _ -> TBool
  | Char  _ -> TChar
  | Str   _ -> TString

let type_cte_env cte_env =
  Env.fold (fun k v e -> Env.add k (type_cte v) e) cte_env Env.empty

let of_type_name ts = function
    Ast.TInt -> TInt
  | Ast.TFloat -> TFloat
  | Ast.TBool -> TBool
  | Ast.TChar -> TChar
  | Ast.TString -> TString
  | Ast.TIdent t when (TypeSet.mem t ts) -> Tname t
  | Ast.TIdent t -> raise (Type_unknown t)

let add_fields h t l =
  List.iter (fun s -> Hashtbl.add h s t) l

let eval_type ts cte_env = function
    Ast.Pointer (t,_) -> Pointer (of_type_name ts t)
  | Ast.Array (l, t, _) ->
      let (n,l) = eval_cexpr (get_int cte_env) l in
	Array (n,l,of_type_name ts t)
  | Ast.Record (l,_) ->
      let fields = Hashtbl.create 13 in
	List.iter
	  (fun (t,l,_) -> add_fields fields (of_type_name ts t) l) l;
	Record fields

let real_type tenv = function
    Tname t -> Env.find t tenv
  | t -> t

(* type algebra/env class *)

class type_env ts =
object (s:'self)
  val env = Hashtbl.create 29
  val mutable cenv = Env.empty
  val tset = ts
  method add (tn:string) (t:ctype) =
    Hashtbl.add env tn t
  method find tn = Hashtbl.find env tn
  method real_type = function
      Tname t -> s#find t
    | t -> t
  method eq t1 t2 =
    match (s#real_type t1, s#real_type t2) with
	(Pointer (TVoid), Pointer _) | (Pointer _, Pointer (TVoid))
	  -> true
      | (TInt,TFloat) | (TFloat,TInt) -> true
      | (rt1,rt2) -> rt1 = rt2
  method make_real_type tn =
    s#real_type (of_type_name ts tn)

  method build_var_list = function
    | (tn,pn) ->
	List.rev_map (fun (n:string) -> (n,s#make_real_type tn)) pn

  method import_cte (c: cte Env.t) =
    cenv <- Env.fold Env.add cenv c

  method get_cte = cenv

  method export_cte =
    Env.fold (fun k v l -> (k,v)::l) cenv []

  method iter f =
    let s = Stack.create () in
      begin
	Hashtbl.iter (fun x y -> Stack.push (x,y) s) env;
	Stack.iter (fun (x,y) -> f x y) s;
      end
  method import (t:'self) =
    s#import_cte t#get_cte;
    t#iter s#add
end

(* Build and validate static typing envirronement *)

let build_static_env d =
  let cte_env = make_cte_env d.Ast.constants Env.empty in
  let ts = build_type_name_set d.Ast.types in
  let te = (new type_env ts) in
    begin
      te#import_cte cte_env;
      (type_cte_env cte_env, ts,
       List.fold_left
	 (fun env (s,td,_) -> env#add s (eval_type ts cte_env td); env)
	 te
	 d.Ast.types
      )
    end

let extend_static_env (c1,ts1,te1) d =
  let cte_env = make_cte_env d.Ast.constants te1#get_cte in
  let c  = Env.fold Env.add c1 (type_cte_env cte_env) in
  let ts = List.fold_left
    (fun s (n,_,_) -> TypeSet.add n s) ts1 d.Ast.types
  in
  let te = new type_env ts in
    te#import te1;
    te#import_cte cte_env;
    try
      (c, ts,
       List.fold_left
	 (fun env (s,td,_) -> env#add s (eval_type ts cte_env td); env)
	 te
	 d.Ast.types
    )
    with
	Type_unknown t ->
	  begin
	    Printf.fprintf stderr "type inconnu %s\n" t;
	    exit 4
	  end

let static_env_fusion (c1,ts1,te1) (c2,ts2,te2) =
  let c  = Env.fold Env.add c2 c1 in
  let ts = TypeSet.union ts1 ts2 in
  let te = new type_env ts in
    begin
      te#import te1;
      te#import te2;
      (c,ts,te)
    end

(* get fields and array bounds *)

exception Type_field_unknown of string
exception Type_not_record

let get_fields f = function
    Record fields ->
      begin
	try Hashtbl.find fields f with
	    Not_found -> raise (Type_field_unknown f)
      end
  | _ -> raise Type_not_record

exception Type_too_dimension of int
exception Type_not_array

let get_nbounds n = function
    Array (nd,dl,_) when n<nd ->
      List.nth dl n
  | Array (_,_,_) -> raise (Type_too_dimension n)
  | _ -> raise Type_not_array

(* Typing *)

exception Gen_type_error

(* type compare *)

let type_eq t1 t2 =
  match (t1,t2) with
      (Pointer (TVoid), Pointer _) | (Pointer _, Pointer (TVoid)) -> true
    | _ -> t1 = t2

(* Operators/functions typing *)

exception Type_mismatch of ctype * ctype
exception Too_many_parameters
exception Not_enough_parameters
exception Not_left_value of (Lexing.position * Lexing.position)

type fun_param = Im of ctype | Ad of ctype

class ['a] funEnv (b:'a) =
object (s)
  val env = Hashtbl.create 53
  val builtins = b
  method add_fun (name:string) (ft:fun_param list * ctype) =
    begin
      s#warning_multiAdd "function" name;
      Hashtbl.replace env name ft;
    end
  method add_proc name pt =
    s#warning_multiAdd "procedure" name;
    Hashtbl.replace env name (pt,TVoid)
  method find n =
    Hashtbl.find env n
  method warning_multiAdd ftype name =
    if (Hashtbl.mem env name) then
      Format.eprintf "@[<h>WARNING: %s %s already exists@]@." ftype name;
  method builtins = b
  initializer
    s#add_proc "ecrire_entier" [Im TInt];
end

let rec is_left_value = function
    Ast.Ident (_,_) -> true
  | Ast.UniOp ("^",_,_) -> true
  | Ast.Field (_,_,_) -> true
  | Ast.Get (_,_,_) -> true
  | _ -> false

let rec apply tenv ft etl = match (ft,etl) with
    (([],tout),[]) -> tout
  | (([],tout),_) -> raise Too_many_parameters
  | ((_,tout),[]) -> raise Not_enough_parameters
  | ((Im h1::t1,tout),(h2,_)::t2) when tenv#eq h1 h2 ->
      apply tenv (t1,tout) t2
  | ((Ad h1::t1,tout),(h2,e)::t2)
      when tenv#eq h1 h2 && is_left_value e ->
      apply tenv (t1,tout) t2
  | ((Ad h1::_,_),(h2,e)::_)
      when tenv#eq h1 h2 ->
      raise (Not_left_value (Ast.get_loc e))
  | ((((Ad h1)|(Im h1))::_,_),(h2,_)::_) -> raise (Type_mismatch (h1,h2))

let type_op tenv op tl = match (op,List.map (tenv#real_type) tl) with
    (("+"|"-"|"*"|"/"|"%"|"div"), [TInt;TInt]) -> TInt
  | (("+"|"-"|"*"|"/"), [TInt|TFloat;TInt|TFloat]) -> TFloat
  | ("-", [(TInt|TFloat) as t]) -> t
  | ("+", [TString;TString]) -> TString
  | ("^", [Pointer t]) -> t
  | ("non", [TBool]) -> TBool
  | ((">"|"<"|"<="|">="|"="|"<>"), [x;y]) when tenv#eq x y -> TBool
  | ((">"|"<"|"<="|">="|"="|"<>"), [x;y]) -> raise (Type_mismatch (x,y))
  | (("et"|"ou"),[TBool;TBool])  -> TBool
  | _ -> raise Gen_type_error

class ['loc] typing_ctx (cte_env,ts,type_env) intype l =
object (s)
  val cte:ctype Env.t = cte_env
  val t_set:TypeSet.t = ts
  val t_env:< eq : ctype -> ctype -> bool; real_type : ctype -> ctype; .. > = type_env
  val inputs: (ctype*'loc Ast.expr) array = Array.of_list intype
  val mutable index = 0
  val loc:'loc = l

  method get_type = fst(inputs.(index))
  method get_inexpr = snd(inputs.(index))
  method is_left_value = is_left_value s#get_inexpr
  method get_cte_t c = Env.find c cte
  method get_type_name t = of_type_name t_set t
  method real_type t = t_env#real_type t
  method eq t1 t2 = t_env#eq t1 t2
  method get_loc = loc
  method get_intype = s#real_type s#get_type

  method reset = index <- -1

  method get_rank = index

  method next_index =
    index <- index + 1;
    index

  method next_type =
    begin
      index <- index + 1;
      fst(inputs.(index))
    end

  method iter_typechk (typechk: 'self -> ctype) =
    if s#next_index < (Array.length inputs) - 1 then
      (ignore (typechk s); s#iter_typechk typechk)
    else
      typechk s
end

(* Expression typing *)

exception Unknown_id of string * (Lexing.position * Lexing.position)
exception Type_error of string * (Lexing.position * Lexing.position)

let raise_type_mismatch context t1 t2 l =
  let s =
    "type "^(ctype2str t1)^" doesn't match type "^(ctype2str t2)^" in "
  in
    raise (Type_error (s,l))

let rec check_expr ((cte_env,ts,type_env) as staticenv) fenv env =
  function
      Ast.Int (_,_) -> TInt
    | Ast.Float (_,_) -> TFloat
    | Ast.Bool (_,_) -> TBool
    | Ast.Char (_,_) -> TChar
    | Ast.Str (_,_) -> TString
    | Ast.Nul _ -> Pointer TVoid
    | Ast.Inf _ -> TInt
    | Ast.Ident (x,l) ->
	begin
	  try Env.find x env with
	      Not_found ->
		try Env.find x cte_env
		with Not_found -> raise (Unknown_id (x,l))
	end
    | Ast.BinOp(op,e1,e2,l) ->
	begin
	  try
	    type_op type_env op
	      [check_expr staticenv fenv env e1;
	       check_expr staticenv fenv env e2]
	  with
	      Type_mismatch (_,_) ->
		raise (Type_error ("wrong type for operator "^op,l))
 	    | _ -> raise (Type_error ("type error",l))
	end
    | Ast.UniOp(op,e,l) ->
	begin
	  try
	    type_op type_env op
	      [check_expr staticenv fenv env e]
	  with
	      Type_mismatch (_,_) ->
		raise (Type_error ("wrong type for operator "^op,l))
	    | Gen_type_error -> raise (Type_error ("type error",l))
	end
    | Ast.FCall (f,el,l) ->
	let etl =
	  List.map
	    (fun e ->
	       (check_expr staticenv fenv env e,e)
	    ) el
	in
	  begin
	    try
	      let ft = fenv#find f
	      in
		try apply type_env ft etl with
		    Type_mismatch (t1,t2) ->
		      raise_type_mismatch "function application" t1 t2 l
	    with
		Not_found ->
		  begin
		    try
		      fenv#builtins#typecheck f
			(new typing_ctx staticenv etl l) l
		    with
			Not_found -> raise (Unknown_id (f,l))
		  end
	  end
    | Ast.Field (e,field,l) ->
	begin
	  let t = check_expr staticenv fenv env e in
	    try
	      get_fields field (type_env#real_type t)
	    with
		Type_field_unknown f ->
		  raise (Type_error ("record has no field named "^f,l))
	      | Type_not_record ->
		  begin
		    Format.eprintf "@[<v>%s@]@." (ctype2str t);
		    raise (Type_error ("expression is not a record",l))
		  end
	end
    | Ast.Get (e,el,l) ->
	let rec all_int n = function
	    [] -> (n,None)
	  | h::t
	      when type_eq TInt (check_expr staticenv fenv env h) ->
	      all_int (n+1) t
	  | h::_ -> (-1,Some (Ast.get_loc h))
	in
	begin
	  match type_env#real_type (check_expr staticenv fenv env e)
	  with
	      Array (d,_,t) ->
		begin
		  match all_int 0 el with
		      (n, None) when n=d -> t
		    | (_, Some l) ->
			raise (Type_error ("array indexes is not an integer",l))
		    | (n,_) when n<d ->
			raise (Type_error ("missing indexes",l))
		    | _ ->
			raise (Type_error ("too much indexes",l))
		end
	    | _ -> raise (Type_error ("expression is not an array",l))
	end

let rec check_instr ret ((cte_env,ts,type_env) as staticenv) fenv env =
  function
      Ast.Affect (e1,e2,l) ->
	if is_left_value e1 then
	  (if not
	     (type_env#eq
		(check_expr staticenv fenv env e1)
		(check_expr staticenv fenv env e2))
	   then
	     raise (Type_error ("types do not agree in affectation",l))
	  )
	else
	  raise (Not_left_value (Ast.get_loc e1))
    | Ast.PCall (p,el,l) ->
	let etl =
	  List.map
	    (fun e ->
	       (check_expr staticenv fenv env e,e)
	    ) el
	in
	  begin
	    try
	      try
		let ft = fenv#find p
		in
		  if not (type_env#eq (apply type_env ft etl) TVoid) then
		    raise (Type_error (p^" is not a procedure",l))
	      with
		  Not_found ->
		    begin
		      try
			ignore(fenv#builtins#typecheck p
				 (new typing_ctx staticenv etl l) l)
		      with
			  Not_found -> raise (Unknown_id (p,l))
		    end
	    with
		Type_mismatch (t1,t2) ->
		  raise_type_mismatch "function application" t1 t2 l
	  end
    | Ast.Return (e,l) ->
	begin
	  if not (
	    type_env#eq ret (check_expr staticenv fenv env e)
	  ) then
	    raise (Type_error ("returned type mismatch",l))
	end
    | Ast.If (e,il,l) ->
	begin
	  if type_eq TBool (check_expr staticenv fenv env e) then
	    List.iter (check_instr ret staticenv fenv env) il
	  else
	    raise
	      (Type_error
		 ("this expression should have type bool",
		  Ast.get_loc e)
	      )
	end
    | Ast.IfElse (e,il1,il2,l) ->
	begin
	  if type_eq TBool (check_expr staticenv fenv env e) then
	    begin
	      List.iter (check_instr ret staticenv fenv env) il1;
	      List.iter (check_instr ret staticenv fenv env) il2;
	    end
	  else
	    raise
	      (Type_error
		 ("this expression should have type bool",
		  Ast.get_loc e)
	      )
	end
    | Ast.While (e,il,l) ->
	begin
	  if type_eq TBool (check_expr staticenv fenv env e) then
	    List.iter (check_instr ret staticenv fenv env) il
	  else
	    raise
	      (Type_error
		 ("this expression should have type bool",
		  Ast.get_loc e)
	      )
	end
    | Ast.DoWhile (e,il,l) ->
	begin
	  if type_eq TBool (check_expr staticenv fenv env e) then
	    List.iter (check_instr ret staticenv fenv env) il
	  else
	    raise
	      (Type_error
		 ("this expression should have type bool",
		  Ast.get_loc e)
	      )
	end
    | Ast.ForUp (i,s,e,il,l) ->
	begin
	  (
	    if not (type_eq TInt (Env.find i env))
	    then
	      raise
		(Type_error
		   ("variable "^i^" should have type int",l)
		)
	  );
	  (
	    if not (type_eq TInt (check_expr staticenv fenv env s))
	    then
	      raise
		(Type_error
		   ("this expression should have type int",
		    Ast.get_loc s)
		)
	  );
	  (
	    if not (type_eq TInt (check_expr staticenv fenv env e))
	    then
	      raise
		(Type_error
		   ("this expression should have type int",
		    Ast.get_loc e)
		)
	  );
	  List.iter (check_instr ret staticenv fenv env) il;
	end
    | Ast.ForDown (i,s,e,il,l) ->
	begin
	  (
	    if not (type_eq TInt (Env.find i env))
	    then
	      raise
		(Type_error
		   ("variable "^i^" should have type int",l)
		)
	  );
	  (
	    if not (type_eq TInt (check_expr staticenv fenv env s))
	    then
	      raise
		(Type_error
		   ("this expression should have type int",
		    Ast.get_loc s)
		)
	  );
	  (
	    if not (type_eq TInt (check_expr staticenv fenv env e))
	    then
	      raise
		(Type_error
		   ("this expression should have type int",
		    Ast.get_loc e)
		)
	  );
	  List.iter (check_instr ret staticenv fenv env) il;
	end
    | Ast.Switch (e,sl,l) ->
	let t = check_expr staticenv fenv env e in
	  begin
	    List.iter (
	      fun (es,il) ->
		if not (type_eq t (check_expr staticenv fenv env es)) then
		  raise (Type_error ("case type mismatch", Ast.get_loc es)
		  );
		List.iter (check_instr ret staticenv fenv env) il;
	    ) sl;
	  end

let rec auto_cast ret ((cte_env,ts,type_env) as staticenv) fenv env =
  function
      Ast.Affect(e1,e2,l) as i->
	begin
	  match (type_env#real_type (check_expr staticenv fenv env e1),
		 type_env#real_type (check_expr staticenv fenv env e2)) with
	      (TInt,TFloat) -> Ast.Affect(e1,Ast.UniOp("f2i",e2,l),l)
	    | (TFloat,TInt) -> Ast.Affect(e1,Ast.UniOp("i2f",e2,l),l)
	    | _             -> i
	end
    | Ast.Return (e,l) as i ->
	begin
	  match (type_env#real_type ret,
		 type_env#real_type (check_expr staticenv fenv env e)) with
	      (TInt,TFloat) -> Ast.Return(Ast.UniOp("f2i",e,l),l)
	    | (TFloat,TInt) -> Ast.Return(Ast.UniOp("i2f",e,l),l)
	    | _             -> i
	end
    | Ast.If(e,il,l) ->
	Ast.If(e,List.map (auto_cast ret staticenv fenv env) il,l)
    | Ast.IfElse (e,il1,il2,l) ->
	Ast.IfElse(e,List.map (auto_cast ret staticenv fenv env) il1,
	       List.map (auto_cast ret staticenv fenv env) il2,l)
    | Ast.While(e,il,l) ->
	Ast.While(e,List.map (auto_cast ret staticenv fenv env) il,l)
    | Ast.DoWhile(e,il,l) ->
	Ast.DoWhile(e,List.map (auto_cast ret staticenv fenv env) il,l)
    | Ast.ForUp (i,s,e,il,l) ->
	Ast.ForUp(i,s,e,List.map (auto_cast ret staticenv fenv env) il,l)
    | Ast.ForDown (i,s,e,il,l) ->
	Ast.ForDown(i,s,e,List.map (auto_cast ret staticenv fenv env) il,l)
    | Ast.Switch (e,sl,l) ->
	Ast.Switch
	  (e,
	   List.map
	     (fun (es,il) ->
		(es, List.map (auto_cast ret staticenv fenv env) il)
	     ) sl,
	   l)
    | i -> i

let rec find_ret = function
    [] -> false
  | (Ast.Return (_,_))::_ -> true
  | Ast.If (_,il,_)::l ->
      find_ret il || find_ret l
  | Ast.IfElse (_,il1,il2,_)::l ->
      find_ret il1 || find_ret il2 || find_ret l
  | Ast.While (_,il,_)::l ->
      find_ret il || find_ret l
  | Ast.DoWhile (_,il,_)::l ->
      find_ret il || find_ret l
  | Ast.ForUp (_,_,_,il,_)::l ->
      find_ret il || find_ret l
  | Ast.ForDown (_,_,_,il,_)::l ->
      find_ret il || find_ret l
  | Ast.Switch (_,sl,_) :: l ->
      List.exists (fun (_,il) -> find_ret il) sl || find_ret l
  | _::l -> find_ret l

exception No_return of string

let check_algo ((cte_env,ts,type_env) as staticenv) fenv = function
    Ast.Function(f,t,pl,pg,vars,il) ->
      let rec make_vect = function
	  [] -> []
	| (tn,pn,_) :: l ->
	    List.map (fun s -> (s,of_type_name ts tn)) pn @ make_vect l
      in
      let tpl = make_vect pl in
      let tpg = make_vect pg in
      let tvar = make_vect vars in
      let env =
	List.fold_left (fun e (n,t) -> Env.add n t e)
	  (List.fold_left (fun e (n,t) -> Env.add n t e)
	     (List.fold_left (fun e (n,t) -> Env.add n t e) Env.empty tpl)
	     tpg)
	  tvar
      in
      let ftparam =
	(List.map (fun (_,t) -> Im t) tpl)
	@ (List.map (fun (_,t) -> Ad t) tpg)
      in
	begin
	  fenv#add_fun f (ftparam,of_type_name ts t);
	  if not (find_ret il) then
	    raise (No_return f);
	  List.iter (check_instr (of_type_name ts t) staticenv fenv env) il;
	end
  | Ast.Procedure(p,pl,pg,vars,il) ->
      let rec make_vect = function
	  [] -> []
	| (tn,pn,_) :: l ->
	    List.map (fun s -> (s,of_type_name ts tn)) pn @ make_vect l
      in
      let tpl = make_vect pl in
      let tpg = make_vect pg in
      let tvar = make_vect vars in
      let env =
	List.fold_left (fun e (n,t) -> Env.add n t e)
	  (List.fold_left (fun e (n,t) -> Env.add n t e)
	     (List.fold_left (fun e (n,t) -> Env.add n t e) Env.empty tpl)
	     tpg)
	  tvar
      in
      let ftparam =
	(List.map (fun (_,t) -> Im t) tpl)
	@ (List.map (fun (_,t) -> Ad t) tpg)
      in
	begin
	  fenv#add_proc p ftparam;
	  List.iter (check_instr (TVoid) staticenv fenv env) il;
	end

let auto_cast_algo ((cte_env,ts,type_env) as staticenv) fenv = function
    Ast.Function(f,t,pl,pg,vars,il) ->
      let rec make_vect = function
	  [] -> []
	| (tn,pn,_) :: l ->
	    List.map (fun s -> (s,of_type_name ts tn)) pn @ make_vect l
      in
      let tpl = make_vect pl in
      let tpg = make_vect pg in
      let tvar = make_vect vars in
      let env =
	List.fold_left (fun e (n,t) -> Env.add n t e)
	  (List.fold_left (fun e (n,t) -> Env.add n t e)
	     (List.fold_left (fun e (n,t) -> Env.add n t e) Env.empty tpl)
	     tpg)
	  tvar
      in
	begin
	  if not (find_ret il) then
	    raise (No_return f);
	  Ast.Function
	    (f,t,pl,pg,vars,
	     List.map (auto_cast (of_type_name ts t) staticenv fenv env) il)
	end
  | Ast.Procedure(p,pl,pg,vars,il) ->
      let rec make_vect = function
	  [] -> []
	| (tn,pn,_) :: l ->
	    List.map (fun s -> (s,of_type_name ts tn)) pn @ make_vect l
      in
      let tpl = make_vect pl in
      let tpg = make_vect pg in
      let tvar = make_vect vars in
      let env =
	List.fold_left (fun e (n,t) -> Env.add n t e)
	  (List.fold_left (fun e (n,t) -> Env.add n t e)
	     (List.fold_left (fun e (n,t) -> Env.add n t e) Env.empty tpl)
	     tpg)
	  tvar
      in
	begin
	  Ast.Procedure
	    (p,pl,pg,vars,
	     List.map (auto_cast (TVoid) staticenv fenv env) il)
	end


let check_entry_point ((cte_env,ts,type_env) as staticenv) fenv = function
    Ast.Main (vars,il) ->
      let rec make_vect = function
	  [] -> []
	| (tn,pn,_) :: l ->
	    List.map (fun s -> (s,of_type_name ts tn)) pn @ make_vect l
      in
      let env =
	List.fold_left (fun e (n,t) -> Env.add n t e) Env.empty (make_vect vars)
      in
	List.iter (check_instr (TVoid) staticenv fenv env) il

