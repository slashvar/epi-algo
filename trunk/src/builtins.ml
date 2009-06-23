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

(* builtins.ml: builtins framework *)

class virtual ['callctx,'typectx,'loc,'out, 'tout] builtin (n:string) =
object (s)
  constraint 'callctx = < get_loc : 'loc; ..>
  val name = n
  method virtual call : 'callctx -> 'out
  method virtual typecheck : 'typectx -> 'tout
  method virtual register_call_site : 'typectx -> 'loc -> unit
  method get_name = name
end

class ['callctx,'typectx,'loc,'out,'tout] builtin_basic n code typechk =
object (s)
  inherit ['callctx,'typectx,'loc,'out,'tout] builtin n
  method call = code
  method typecheck = typechk
  method register_call_site _ _ = ()
end

class ['callctx,'typectx,'loc,'out,'tout] builtin_poly n typechk =
object (s)
  inherit ['callctx,'typectx,'loc,'out,'tout] builtin n
  val call_sites = Hashtbl.create 53
  val mutable code = fun _ _ -> assert false
  method typecheck tc =
    s#register_call_site tc tc#get_loc;
    typechk tc
  method register_call_site t l =
    Hashtbl.add call_sites l t
  method init_code c = code <- c
  method call cc =
    let tc = Hashtbl.find call_sites (cc#get_loc) in
      code cc tc#get_intype
end

exception Unsupported_input of string

class ['callctx,'typectx,'loc,'intype,'out,'tout] builtin_overload n typechk =
object (s)
  inherit ['callctx,'typectx,'loc,'out,'tout] builtin_poly n typechk
  val overload = Hashtbl.create 53
  method overload (t:'intype) c =
    Hashtbl.add overload t c
  method call cc =
    try
      let tc = (Hashtbl.find call_sites (cc#get_loc)) in
	(Hashtbl.find overload tc#get_intype) cc tc
    with
	Not_found -> raise (Unsupported_input name)
end

class ['callctx,'typectx,'loc,'out,'tout,'intype] builtin_var_overload n typechk =
object (s)
  inherit ['callctx,'typectx,'loc,'intype,'out,'tout] builtin_overload n typechk

  method typecheck tc =
    begin
      s#register_call_site tc tc#get_loc;
      tc#reset;
      tc#iter_typechk typechk;
    end

  method call cc =
    try
      begin
	let tc = (Hashtbl.find call_sites (cc#get_loc)) in
	  tc#reset;
	  cc#reset;
	  cc#iter_call (s#next_call tc);
      end
    with
	Not_found -> raise (Unsupported_input name)

  method build_variadic l =
    List.iter (fun (t,c) -> s#overload t c) l

  method next_call tc cc =
    (Hashtbl.find overload tc#next_type) cc tc

end

class ['callctx,'typectx,'loc,'intype,'out,'tout] builtin_var n code typechk =
object (s)

  inherit ['callctx,'typectx,'loc,'out,'tout] builtin_basic n
    (fun cc -> cc#reset ; cc#iter_call code)  typechk

end

class ['callctx,'typectx,'loc,'intype,'out,'tout,'a] builtin_env =
object (s)
  constraint 'a = ('callctx,'typectx,'loc,'out,'tout) #builtin

  val env = Hashtbl.create 53

  method add (b:'a) =
    Hashtbl.add env b#get_name b

  method call n cc =
    (Hashtbl.find env n)#call cc

  method typecheck n tc l =
    let o = (Hashtbl.find env n)#typecheck tc in
      begin
	(Hashtbl.find env n)#register_call_site tc l;
	o
      end

end
