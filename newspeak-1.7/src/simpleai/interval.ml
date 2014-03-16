open UnrelState

type t =
  | Top
  | Val of Int32.t * Int32.t

let lt x y = Int32.compare x y < 0
let lte x y = Int32.compare x y <= 0
(*let eq x y = Int32.compare x y = 0*)
let gt x y = Int32.compare x y > 0
let gte x y = Int32.compare x y >= 0
let min x y = if lt x y then x else y
let max x y = if gt x y then x else y
let min64 x y = if Int64.compare x y < 0 then x else y
let max64 x y = if Int64.compare x y > 0 then x else y
let lt_min32 x64 =
  Int64.compare x64 (Int64.of_int32 Int32.min_int) < 0
let gt_max32 x64 =
  Int64.compare x64 (Int64.of_int32 Int32.max_int) > 0

let to_string = function
  | Val (x, y) -> Printf.sprintf "[%s, %s]" (Int32.to_string x) (Int32.to_string y)
  | _ -> "?"

let normalize v =
  match v with
  | Top -> Top
  | Val (x, y) ->
    assert (lte x y);
    if x = Int32.min_int && y = Int32.max_int then Top
    else v

let universe = Top

let singleton x = Val (x, x)

let of_bounds (i1, i2) = normalize (Val (i1, i2))

let contains x y =
  match x, y with
    | Top, _ -> true
    | Val (x1, y1), Val (x2, y2) ->
	lte x1 x2 && gte y1 y2 
    | _ -> false

let join x y =
  match x, y with
  | Val (x1, y1), Val (x2, y2) -> normalize (Val (min x1 x2, max y1 y2))
  | _ -> Top

let widen x y =
  match x, y with
  | Val (a, b), Val (c, d) ->
    let x = if lte a c then a else Int32.min_int in
    let y = if gte b d then b else Int32.max_int in
    normalize (Val (x, y))
  | _ -> Top

let implies = function
  | Val (x, y), Simple.Equals, i32 -> x = i32 && y = i32
  | Val (_, y), Simple.IsLess, i32 -> lt y i32
  | _ -> false

let neg v =
  let zero = Int32.zero in
  match v with
  | Val (x, y) ->
    if x = zero && y = zero then Val (Int32.one, Int32.one)
    else if lt y zero || gt x zero then Val (zero, zero)
    else Top
  | _ -> Top
      

let match_val_bounds x64 y64 =
  (* both are more than max *)
  if gt_max32 x64 then
    Top
  (* both are less than min *)
  else if lt_min32 y64 then
    Top
  else
    let x32, y32 = Int64.to_int32 x64, Int64.to_int32 y64 in
    match lt_min32 x64, gt_max32 y64 with
    | true, true -> Top
    | true, false -> normalize (Val (Int32.min_int, y32))
    | false, true -> normalize (Val (x32, Int32.max_int))
    | false, false -> normalize (Val (x32, y32))

let add x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.add (Int64.of_int32 a) (Int64.of_int32 c) in
	let y64 = Int64.add (Int64.of_int32 b) (Int64.of_int32 d) in
	match_val_bounds x64 y64
    | _ -> Top

let sub x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.sub (Int64.of_int32 a) (Int64.of_int32 d) in
	let y64 = Int64.sub (Int64.of_int32 b) (Int64.of_int32 c) in
	match_val_bounds x64 y64
    | _ -> Top

let cartesian_product op (a, b) (c, d) =
  [op a c; op a d; op b c; op b d]

let contains_zero = function
  | Val (a, b) -> lte a Int32.zero && gte b Int32.zero
  | Top -> true

let mul x y =
  match x, y with
  | Val (a, b), Val (c, d) ->
    let my_mul x y = Int64.mul (Int64.of_int32 x) (Int64.of_int32 y) in
    let prod_cart64 = cartesian_product my_mul (a, b) (c, d) in
    let min64 = List.fold_right min64 prod_cart64 Int64.max_int in
    let max64 = List.fold_right max64 prod_cart64 Int64.min_int in
    match_val_bounds min64 max64
  | _ -> Top

let rec div x y =
  match x, y with
  | Val (a, b), Val (c, d) ->
    if contains_zero y then
	  (* dividing x by y without 0 *)
      if lt c Int32.zero || gt d Int32.zero then
	join (div x (Val (c, max c Int32.minus_one))) (div x (Val (min d Int32.one, d)))
      else
	Top
    else
      let my_div x y = Int64.div (Int64.of_int32 x) (Int64.of_int32 y) in
      let prod_cart64 = cartesian_product my_div (a, b) (c, d) in
      let min64 = List.fold_right min64 prod_cart64 Int64.max_int in
      let max64 = List.fold_right max64 prod_cart64 Int64.min_int in
      match_val_bounds min64 max64
  | _ -> Top

let rec rem x y =
  match x, y with
  | Val (a, b), Val (c, d) ->
    if contains_zero y then
      if lt c Int32.zero || gt d Int32.zero then
	join (rem x (Val (c, max c Int32.minus_one))) (rem x (Val (min d Int32.one, d)))
      else
	Top
    else
      let my_rem x y = Int64.rem (Int64.of_int32 x) (Int64.of_int32 y) in
      let prod_cart64 = cartesian_product my_rem (a, b) (c, d) in
      let min64 = List.fold_right min64 prod_cart64 Int64.max_int in
      let max64 = List.fold_right max64 prod_cart64 Int64.min_int in
      match_val_bounds min64 max64
  | _ -> Top

(* is_safe_val : t -> bool *)
let is_safe_binop ?is_safe_val op32 op64 x y =
  let is_safe_val = match is_safe_val with None -> fun _ -> true | Some f -> f in
  match (x, y) with
    | Val (a, b), Val (c, d) ->
	let to_64 x32 y32 = op64 (Int64.of_int32 x32) (Int64.of_int32 y32) in
	(* we must check val first (may contains zero) *)
	  is_safe_val y 
	  &&
	    List.for_all2
	    (fun x32 x64 -> Int64.compare (Int64.of_int32 x32) x64 = 0)
	    (cartesian_product op32 (a, b) (c, d))
	    (cartesian_product to_64 (a, b) (c, d))
    | _ -> false

let is_safe_add = is_safe_binop Int32.add Int64.add

let is_safe_sub = is_safe_binop Int32.sub Int64.sub

let is_safe_mul = is_safe_binop Int32.mul Int64.mul

let is_safe_div = is_safe_binop ~is_safe_val:(fun x -> not (contains_zero x)) Int32.div Int64.div

let is_safe_mod = is_safe_binop ~is_safe_val:(fun x -> not (contains_zero x)) Int32.rem Int64.rem

	  
let guard op cond x =
  let one = Int32.one in
  normalize (
  match cond, op, x with
  | Val (_, b), GTE, Val (c, d) ->
    if lt b c then raise Emptyset
    else Val (c, min b d)
  | Val (a, _), LTE, Val (c, d) ->
    if gt a d then raise Emptyset
    else Val (max a c, d)
  | Val (_, b), GT, Val (c, d) ->
    if lte b c then raise Emptyset
    else Val (c, min (Int32.sub b one) d)
  | Val (a, _), LT, Val (c, d) ->
    if gte a d then raise Emptyset
    else Val (max (Int32.add a one) c, d)
  | Val _, EQ, Val _ ->
    if contains x cond then cond else raise Emptyset
  | Val (a, b), NEQ, Val (c, d) ->
    if contains cond x then raise Emptyset
    else if contains x cond || lt b c || lt d a then x
    else if lt c a then Val (c, Int32.sub a one)
    else Val (Int32.add b one, d)
  | Val (_, b), GTE, Top ->
    Val (Int32.min_int, b)
  | Val (a, _), LTE, Top ->
    Val (a, Int32.max_int)
  | Val (_, b), GT, Top ->
    Val (Int32.min_int, Int32.sub b one)
  | Val (a, _), LT, Top ->
    Val (Int32.add a one, Int32.max_int)
  | _, EQ, Top -> cond
  | _ -> x)
