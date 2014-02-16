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

open UnrelState

type t = 
    Top
  | Val of Int32.t

let universe = Top

let singleton i = Val i

let of_bounds (l, u) =  if Int32.compare l u = 0 then Val l else Top

let contains x y =
  match (x, y) with
      (Top, _) -> true
    | (Val i, Val j) when i = j -> true
    | _ -> false

let join x y =
  match (x, y) with
      (Val x, Val y) when x = y -> Val x
    | _ -> Top

let widen = join

let neg x =
  match x with
      Val i when i = Int32.zero -> Val Int32.one
    | Val _ -> Val Int32.zero
    | Top -> Top


let apply_binop op32 op64 x y =
  match (x, y) with
      (Val x, Val y) -> 
	let z = op32 x y in
          if (Int64.compare (op64 (Int64.of_int32 x) (Int64.of_int32 y)) (Int64.of_int32 z) != 0) then Top
	  else Val z
    | _ -> Top

let add = apply_binop Int32.add Int64.add

let sub = apply_binop Int32.sub Int64.sub

let mul = apply_binop Int32.mul Int64.mul

let div = apply_binop Int32.div Int64.div

let rem = apply_binop Int32.rem Int64.rem

let is_safe_binop op32 op64 x y =
  match (x, y) with
      (Val x, Val y) ->
	let z = op32 x y in
         (Int64.compare (op64 (Int64.of_int32 x) (Int64.of_int32 y)) (Int64.of_int32 z) == 0) 
    | _ -> false

let is_safe_add = is_safe_binop Int32.add Int64.add

let is_safe_sub = is_safe_binop Int32.sub Int64.sub

let is_safe_mul = is_safe_binop Int32.mul Int64.mul

let is_safe_div = is_safe_binop Int32.div Int64.div

let is_safe_mod = is_safe_binop Int32.rem Int64.rem

let implies = function
  | Val i1, Simple.Equals, i2 -> Int32.compare i1 i2 = 0
  | Val i1, Simple.IsLess, i2 -> Int32.compare i1 i2 < 0
  | _ -> false

(* Restricts the value x to make the condition 
   c op x true *)
let guard op c x =
  match c, x with
    | Val cval, Val xval ->
	let val_cmp = Int32.compare cval xval in
	let cond = match op with
	  | LTE -> val_cmp <= 0
	  | EQ -> val_cmp = 0
	  | GT -> val_cmp > 0
	  | LT -> val_cmp < 0
	  | NEQ -> val_cmp <> 0
	  | GTE -> val_cmp >= 0
	in
	  if cond then x else raise Emptyset
    | _ -> x

let to_string v = 
  match v with
      Val i -> Int32.to_string i
    | Top -> "?"
