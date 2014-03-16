(*
  C2Newspeak: compiles C code into Newspeak. Newspeak is a minimal language 
  well-suited for static analysis.
  Copyright (C) 2007  Charles Hymans
  
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
*)

open Simple

module Map = Map.Make(struct type t = Simple.vid let compare = compare end)

exception Emptyset
exception Unknown

type bop = EQ | GT | LT | NEQ | LTE | GTE
let bop_to_string = function
  | EQ -> "EQ" | GT -> "GT" | LT -> "LT"
  | NEQ -> "NEQ" | LTE -> "LTE" | GTE -> "GTE"

module type Data =
sig
  type t

  val universe: t
  val singleton: Int32.t -> t
  val of_bounds: (Int32.t * Int32.t) -> t
  val join: t -> t -> t
  val widen : t -> t -> t
  val contains: t -> t -> bool
  val implies: (t * Simple.cmp * Int32.t) -> bool
  val neg: t -> t
  val add: t -> t -> t
  val sub: t -> t -> t
  val mul: t -> t -> t
  val div: t -> t -> t
  val rem: t -> t -> t
  val is_safe_add: t -> t -> bool
  val is_safe_sub: t -> t -> bool
  val is_safe_mul: t -> t -> bool
  val is_safe_div: t -> t -> bool
  val is_safe_mod: t -> t -> bool
  val guard: bop -> t -> t -> t
  val to_string: t -> string
end



module Make(Val: Data) =
struct
  (* None is emptyset *)
  type t = Val.t Map.t option

  let to_string s = 
    match s with
    | None -> "{}"
    | Some s -> 
      let res = ref "" in
      let string_of_info x v =
	let v = Val.to_string v in
	res := Printf.sprintf "%s\n%s -> %s" !res x v
      in
      Map.iter string_of_info s;
      !res

  let read s x = 
    try Map.find x s 
    with Not_found -> invalid_arg ("CstState.read: variable "^x^" not declared")
      
  let universe = Some Map.empty
    
  let contains s1 s2 =
    match s1, s2 with
    | _, None -> true
    | None, _ -> false
    | Some s1, Some s2 ->
      (* for each constraint in s1 there should be a stricter constraint in s2 *)
      try
	let has_constraint x v1 =
	  let v2 = read s2 x in
	  if not (Val.contains v1 v2) then raise Exit
	in
	Map.iter has_constraint s1;
	true
      with Exit -> false
	

  let join s1 s2 = 
    match (s1, s2) with
      (None, s) | (s, None) -> s
    | (Some s1, Some s2) -> 
      let res = ref Map.empty in
      let join_info x v1 =
	let v2 = read s2 x in
	let v = Val.join v1 v2 in
	res := Map.add x v !res
      in
      Map.iter join_info s1;
      Some !res

  let widen s1 s2 =
    match s1, s2 with
    | None, s | s, None -> s
    | Some s1, Some s2 ->
      let res = ref Map.empty in
      let join_info x v1 =
	let v2 = read s2 x in
	let v = Val.widen v1 v2 in
	res := Map.add x v !res
      in
      Map.iter join_info s1;
      Some !res
	
  let add_var x s = 
    match s with
      Some s -> Some (Map.add x Val.universe s)
    | None -> None
      
  let eval_lval lv =
    match lv with
      Global x -> x
	
  let apply_binop op x y =
    match op with
      PlusI -> Val.add x y
    | MinusI -> Val.sub x y
    | MultI -> Val.mul x y
    | DivI -> Val.div x y
    | Mod -> Val.rem x y
    | Gt | Eq -> failwith "Unsupported binary operator"

  let rec eval_exp s e =
    match e with
      Const CInt i -> Val.singleton i
    | Lval Global x -> read s x
    | Random b -> Val.of_bounds b
    | UnOp (Not, e) -> Val.neg (eval_exp s e)
    | BinOp (op, e1, e2) -> 
      let v1 = eval_exp s e1 in
      let v2 = eval_exp s e2 in
      apply_binop op v1 v2
	
  let assign lv e s = 
    match s with
      None -> None
    | Some s -> 
      let x = eval_lval lv in
      let v = eval_exp s e in
      Some (Map.add x v s)
	
  let exp_to_eq e s =
    let rec translate e =
      match e with
      | BinOp (Eq, Lval Global x, e) -> (x, EQ, eval_exp s e)
      | BinOp (Eq, e,Lval Global x) -> (x, EQ, eval_exp s e)

      | BinOp (Gt, e, Lval Global x) -> (x, GT, eval_exp s e)
      | BinOp (Gt,  Lval Global x,e) -> (x, LT, eval_exp s e)

      | UnOp (Not, BinOp (Eq, Lval Global x, e)) -> (x, NEQ, eval_exp s e)
      | UnOp (Not, BinOp (Eq, e, Lval Global x)) -> (x, NEQ, eval_exp s e)

      | UnOp (Not, BinOp (Gt, Lval Global x, e)) -> (x, GTE, eval_exp s e)
      | UnOp (Not, BinOp (Gt, e, Lval Global x)) -> (x, LTE, eval_exp s e)

      | UnOp (Not,UnOp (Not,e)) -> translate e

      | _ -> raise Unknown
    in
    translate e
      
  let guard e s =
    match s with
      None -> None
    | Some s -> 
      try
	let (x, op, c) = exp_to_eq e s in
	let v = read s x in
	let v = Val.guard op c v in
	Some (Map.add x v s)
      with Unknown -> Some s
      | Emptyset -> None

  let implies s (lv, cmp, c) =
    match s with
      None -> true
    | Some s ->
      let x = eval_lval lv in
      let v = read s x in
      let c =
	match c with
	  CInt i -> i
      in
      Val.implies (v, cmp, c)

  let is_safe_binop s (op, e1, e2) = 
    match s with
      None -> true
    | Some s -> 
      let v1 = eval_exp s e1 in
      let v2 = eval_exp s e2 in
      match op with
	PlusI -> Val.is_safe_add v1 v2
      | MinusI -> Val.is_safe_sub v1 v2
      | MultI -> Val.is_safe_mul v1 v2
      | DivI -> Val.is_safe_div v1 v2
      | Mod -> Val.is_safe_mod v1 v2
      | Eq | Gt -> true
	

end

(************************)
(* Disjonctive analisis *)
(************************)


module MakeDisjonctive(Val: Data) =
struct
  module Classic = Make(Val)
    
  type t = Classic.t list
      
  let to_string sl = 
    match sl with
    | [] -> "{}"
    | hd :: rem -> 
      if !Context.final_print then
	Classic.to_string (List.fold_left Classic.join hd rem)
      else
	String.concat ",\n   "
	  (List.map Classic.to_string sl)

  let add_var id = List.map (Classic.add_var id)
      
  let universe = [Classic.universe]

  let clean_list l =
    List.fold_left (fun acc s ->
      if List.exists (fun acc_s -> Classic.contains acc_s s) acc
      then acc else s :: acc) [] l
    
  let contains sl1 sl2 =
    List.for_all (fun y ->
      List.exists (fun x -> Classic.contains x y) sl1)
      sl2

  let join sl1 sl2 = clean_list (sl1 @ sl2)
    
  let widen sl1 sl2 =
    clean_list (
      List.fold_left (fun acc1 s1 ->
	List.fold_left (fun acc2 s2 ->
	  Classic.widen s1 s2 :: acc2
	) acc1 sl2
      ) [] sl1 )
 
  let assign lv e = List.map (Classic.assign lv e)
      
  let guard e sl = clean_list (List.map (Classic.guard e) sl)

  let implies sl ass = List.for_all (fun s -> Classic.implies s ass) sl

  let is_safe_binop sl binop = List.for_all (fun s -> Classic.is_safe_binop s binop) sl
	      

end
