(*
  C2Newspeak: compiles C code into Newspeak. Newspeak is a minimal language 
  well-suited for static analysis.
  Copyright (C) 2007-2011  Charles Hymans, Sarah Zennou
  
  This library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.
  
  This library is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.
  
  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

  Charles Hymans
  EADS Innovation Works - SE/CS
  12, rue Pasteur - BP 76 - 92152 Suresnes Cedex - France
  email: charles.hymans@penjili.org

  Sarah Zennou
  email: sarah(dot)zennou(at)eads(dot)net
*)

open Simple

module State = UnrelState.Make(Interval)
let state_pool = State.t list

let add_globals globals s =
  List.fold_left (fun s' x -> State.add_var x s') s globals
    
let unroll_loop loc cond body =
  let rec loop m =
    if m = 0 then
      While (cond, body)
    else
      If (cond, body @ [(loop (m - 1), loc)], [])
  in
  loop !Context.unroll_number

let rec unroll_stmt prog (stmtk, loc) =
  match stmtk with
  | Set _ -> stmtk, loc
  | If (cond, b1, b2) ->
    If (cond, unroll_blk prog b1, unroll_blk prog b2), loc
  | While (cond, b) ->
    unroll_loop loc cond (unroll_blk prog b), loc
  | Call (FunId f) ->
    Hashtbl.replace
      prog.fundecs f
      (unroll_blk prog (Hashtbl.find prog.fundecs f));
    stmtk, loc
  | Assert _ -> stmtk, loc
    

and unroll_blk prog blk = List.map (unroll_stmt prog) blk
  

let fixpoint f s =
  let rec loop s n =
    let new_s = f s in
    if State.contains s new_s then
      begin
	Printf.printf "Fixpoint found : %s\n" (State.to_string s);
	s
      end
    else if n > 0 then
	(* Delayed widening *)
      loop (State.join s new_s) (n - 1)
    else
      loop (State.widen s new_s) n
  in
  loop s !Context.delayed_widening_number

let check_exp loc e s =
  let rec check e =
    match e with
      UnOp (_, e) -> check e
    | BinOp (op, e1, e2) ->
      check e1;
      check e2;
      if not (State.is_safe_binop s (op, e1, e2)) then begin
	print_endline (Simple.string_of_loc loc^": "
		       ^"potential invalid operation: "
		       ^(Simple.string_of_binop op))
      end
    | _ -> ()
  in
  check e

let compute prog = 
  let rec compute_blk x sp =
    match x with
      x::tl -> 
	let sp = compute_stmt x sp in
	compute_blk tl sp
    | [] -> sp
      
  and compute_stmt (x, loc) sp =
    Printf.printf "%s: %s\n"
      (Simple.string_of_loc loc)
      (String.concat "\n   " (List.map State.to_string sp));
    compute_stmtkind loc x sp
      
  and compute_stmtkind loc x sp =
    match x with
      |	Set (lv, e) -> 
	  List.iter (check_exp loc e) sp;
	  List.map (State.assign lv e) sp
      | Call FunId f -> 
	  let body = 
	    try Hashtbl.find prog.fundecs f
	    with Not_found -> 
	      invalid_arg ("Fixpoint.compute_stmtkind: unknown function "^f)
	  in
	    print_endline ("Call function: "^f);
	    let sp = compute_blk body sp in
	      print_endline ("Return from function: "^f);
	      sp
      | If (e, br1, br2) -> 
	  (*Printf.printf "If %s\n" (string_of_exp e);*)
	  List.iter (check_exp loc e) sp;
	  (*Printf.printf "If with initial state %s\n" (State.to_string s);*)
	  let sp1 = List.map (State.guard e) sp in
	  let sp2 = List.map (State.guard (UnOp (Not, e))) sp in
	    (*Printf.printf "If guarded with s2 = %s\n" (State.to_string s2);*)
	  let sp1 = compute_blk br1 sp1 in
	  let sp2 = compute_blk br2 sp2 in
	    (*Printf.printf "If computed with\n  s1 = %s\n  s2 = %s\n" (State.to_string s1) (State.to_string s2);*)
	    (*State.join s1 s2*)
	    sp1 @ sp2
      | While (e, body) ->
	  let f s =
	    check_exp loc e s;
	    let s = State.guard e s in
	      compute_blk body s
	  in
	  let sp = List.map (fixpoint f) sp in
	  let sp = List.map (State.guard (UnOp (Not, e))) sp in
	    sp
      | Assert a -> 
	  if not (List.forall (fun s -> State.implies s a) sp)
	  then print_endline (Simple.string_of_loc loc^": assertion violation");
	  sp
  in
    
    
    print_endline "Analysis starts";
    let s = State.universe in
  let s = add_globals prog.globals s in
  let sp = compute_blk prog.init [s] in
  let body =
    try Hashtbl.find prog.fundecs "main"
    with Not_found -> invalid_arg "Fixpoint.compute: no main function"
  in
  let body = if !Context.unroll_mode then unroll_blk prog body else body in
  Printf.printf "Unrolled body :\n%s\n" (string_of_blk body);
  let sp = compute_blk body sp in
  Printf.printf "Final states :\n%s"
    (String.concat "\n  "  (List.map State.to_string sp))
	
