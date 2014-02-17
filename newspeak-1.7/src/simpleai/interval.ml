open UnrelState

type t =
  | Top
  | Val of Int32.t * Int32.t

let lt x y = Int32.compare x y < 0
let lte x y = Int32.compare x y <= 0
let eq x y = Int32.compare x y = 0
let gt x y = Int32.compare x y > 0
let gte x y = Int32.compare x y >= 0
let min x y = if lt x y then x else y
let max x y = if gt x y then x else y
let lt_min32 x64 =
  Int64.compare x64 (Int64.of_int32 Int32.min) < 0
let gt_max32 x64 =
  Int64.compare x64 (Int64.of_int32 Int32.max) > 0

let univers = Top

let singleton x = Val (x, x)

let of_bounds i1 i2 = Val (i1, i2)

let contains x y =
  match x, y with
    | Top, _ -> true
    | Val (x1, y1), Val (x2, y2) ->
	lte x1 x2 && gte y1 y2 
    | _ -> false

let join x y =
  match x, y with
  | Val (x1, y1), Val (x2, y2) -> Val (min x1 x2, max y1 y2)
  | _ -> Top

let widen x y = failwith "TODO : interval widening"

let implies = failwith "implies"

let neg = failwith "neg"

let apply_binop op32 op64 x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = op64 (Int64.of_int32 a) (Int64.of_int32 c) in
	let y64 = op64 (Int64.of_int32 b) (Int64.of_int32 d) in
	  if lt_min32 x64 || gt_max32 y64 then
	    Top
	  else
	    Val (op32 a c, op32 b d)
    | _ -> Top

let add x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.add (Int64.of_int32 a) (Int64.of_int32 c) in
	let y64 = Int64.add (Int64.of_int32 b) (Int64.of_int32 d) in
	  if lt_min32 x64 || gt_max32 y64 then
	    Top
	  else
	    Val (Int32.add a c, Int32.add b d)
    | _ -> Top

let sub x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.sub (Int64.of_int32 a) (Int64.of_int32 d) in
	let y64 = Int64.sub (Int64.of_int32 b) (Int64.of_int32 c) in
	  if lt_min32 x64 || gt_max32 y64 then
	    Top
	  else
	    Val (Int32.sub a d, Int32.sub b c)
    | _ -> Top

let mul x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	
