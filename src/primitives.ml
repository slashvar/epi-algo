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

(* primitives.ml: Building primitive of the language *)
(*
  Each primitive is define using a class from <builtins.ml> depending
  on its prototype
*)

(* allocate and free pointer *)

(* allocation : "allouer" *)
let builtin_allouer_code
    (cc :
       ((Lexing.position * Lexing.position), Memory.memory)
       Memory.callctx
    ) t =
  let (get, set) = cc#glob_arg in
  let init_val = cc#get_cs#get_init in
  let p = cc#get_mem#alloc in
  let t = match t with | Typing.Pointer x -> x | _ -> assert false
  in
    (set (Memory.Pointer p);
     cc#get_mem#set p (init_val#build_value t);
     Memory.Nul)

let builtin_allouer_typecheck
    (tc :
       (Lexing.position * Lexing.position) Typing.typing_ctx
    ) =
  if tc#is_left_value
  then
    begin
      match tc#real_type tc#get_intype with
	| Typing.Pointer _ -> Typing.TVoid
	| t ->
            raise
	      (Typing.Type_mismatch (t, Typing.Pointer Typing.TVoid))
    end
  else raise (Typing.Not_left_value (Ast.get_loc tc#get_inexpr))

let builtin_allouer =
  let b = new Builtins.builtin_poly "allouer" builtin_allouer_typecheck
  in
    (b#init_code builtin_allouer_code;
     (b :
       (((Lexing.position * Lexing.position), Memory.memory) Memory.callctx,
         (Lexing.position * Lexing.position) Typing.typing_ctx,
         (Lexing.position * Lexing.position), Memory.value, Typing.
         ctype) Builtins.builtin_poly :>
       (((Lexing.position * Lexing.position), Memory.memory) Memory.
          callctx,
         (Lexing.position * Lexing.position) Typing.typing_ctx,
         (Lexing.position * Lexing.position), Memory.value, Typing.
         ctype) Builtins.builtin))

(* free pointer: "liberer" *)
let builtin_liberer_code cc =
  begin
    (match cc#get_arg with
      | Some (Memory.Pointer p) -> cc#get_mem#free p
      | Some Memory.Nul -> ()
      | _ -> assert false);
    Memory.Nul;
  end

let builtin_liberer_typecheck tc =
  match tc#real_type tc#get_intype with
  | Typing.Pointer _ -> Typing.TVoid
  | t -> raise (Typing.Type_mismatch (t, Typing.Pointer Typing.TVoid))

let builtin_liberer =
  new Builtins.builtin_basic "liberer" builtin_liberer_code
    builtin_liberer_typecheck

(* compute log(n) in float *)
let builtin_log_code cc =
  begin
    match cc#get_arg with
      | Some (Memory.Float f) -> Memory.Float (log f)
      | _ -> assert false
  end

let builtin_log_typecheck tc =
  match tc#real_type tc#get_intype with
    | Typing.TFloat -> Typing.TFloat
    | t -> raise (Typing.Type_mismatch (t, Typing.TFloat))

let builtin_log =
  new Builtins.builtin_basic "log" builtin_log_code
    builtin_log_typecheck

(* output value on stdout: "ecrire" *)
let builtin_ecrire_code cc =
  match cc#get_arg with
  | Some v -> (Printf.printf "%s" (Memory.value2str v);flush stdout;Memory.Nul)
  | _ -> (flush stdout; Memory.Nul)

let builtin_ecrire_typecheck tc = Typing.TVoid

let builtin_ecrire =
  new Builtins.builtin_var "ecrire" builtin_ecrire_code
    builtin_ecrire_typecheck

(* read values on std input: "lire" *)
exception Unsuported_input_type of Typing.ctype
exception Bad_input of (Lexing.position * Lexing.position)
let builtin_lire_code cc t =
  let (_, set) = cc#glob_arg in
    try
      begin
	match t with
	    Typing.TInt -> Scanf.scanf " %d"
	      (fun x -> set (Memory.Int x))
	  | Typing.TBool -> Scanf.scanf " %B"
	      (fun x -> set (Memory.Bool x))
	  | Typing.TChar -> Scanf.scanf " %c"
	      (fun x -> set (Memory.Char x))
	  | Typing.TString -> Scanf.scanf " %s"
	      (fun x -> set (Memory.Str x))
	  | Typing.TFloat -> Scanf.scanf " %f"
	      (fun x -> set (Memory.Float x))
	  | _ -> raise (Unsuported_input_type t)
      end;
      Memory.Nul
    with
	Scanf.Scan_failure _ ->
	  raise (Bad_input cc#get_loc)

let builtin_lire =
  let b = new Builtins.builtin_poly "lire" builtin_ecrire_typecheck
  in
    b#init_code builtin_lire_code;
    (b :
       (((Lexing.position * Lexing.position), Memory.memory) Memory.
          callctx,
        (Lexing.position * Lexing.position) Typing.typing_ctx,
        (Lexing.position * Lexing.position), Memory.value, Typing.
          ctype) Builtins.builtin_poly :>
       (((Lexing.position * Lexing.position), Memory.memory) Memory.
          callctx,
        (Lexing.position * Lexing.position) Typing.typing_ctx,
        (Lexing.position * Lexing.position), Memory.value, Typing.
          ctype) Builtins.builtin)

(* Global builtins env *)
let builtins () =
  let b = new Builtins.builtin_env
  in
    begin
      b#add builtin_liberer;
      b#add builtin_ecrire;
      b#add builtin_allouer;
      b#add builtin_lire;
      b#add builtin_log;
      b
    end
