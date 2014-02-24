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

let match_val_bounds b1 b2 x32 y32 =
  match b1, b2 with
    | true, true -> Top
    | true, false -> Val (Int32.min_int, y32)
    | false, true -> Val (x32, Int32.max_int)
    | false, false -> Val (x32, y32)

let add x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.add (Int64.of_int32 a) (Int64.of_int32 c) in
	let y64 = Int64.add (Int64.of_int32 b) (Int64.of_int32 d) in
	let x32 = Int32.add a c in
	let y32 = Int32.add b d in
	  match_val_bounds (lt_min32 x64) (gt_max32 y64) x32 y32
    | _ -> Top

let sub x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let x64 = Int64.sub (Int64.of_int32 a) (Int64.of_int32 d) in
	let y64 = Int64.sub (Int64.of_int32 b) (Int64.of_int32 c) in
	let x32 = Int32.sub a d in
	let y32 = Int32.add b c in
	  match_val_bounds (lt_min32 x64) (gt_max32 y64) x32 y32
    | _ -> Top

let cartesian_product op (a, b) (b, c) =
  [op a c; op a d; op b c; op b d]

let contains_zero (Val (a, b)) = lte a Int32.zero && gte b Int32.zero

let mul x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	let my_mul x y = Int64.mul (Int64.of_int32 x) (Int64.of_int32 y) in
	let prod_cart32 = [Int32.mul a c; Int32.mul a d; Int32.mul b c; Int32.mul b d] in
	let prod_cart64 = [my_mul a c; my_mul a d; my_mul b c; my_mul b d] in
	let exists_min_int = List.exists lt_min32 prod_cart64 in
	let exists_max_int = List.exists gt_max32 prod_cart64 in
	let min32 = List.fold_right min prod_cart32 Int32.max_int in
	let max32 = List.fold_right max prod_cart32 Int32.min_int in
	  match_val_bounds exists_min_int exists_max_int min32 max32
    | _ -> Top

let div x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	if contains_zero y then
	  failwith "oulala c'est pas cool"
	else
	  begin
	    let my_div x y = Int64.div (Int64.of_int32 x) (Int64.of_int32 y) in
	    let prod_cart32 = [Int32.div a c; Int32.div a d; Int32.div b c; Int32.div b d] in
	    let prod_cart64 = [my_div a c; my_div a d; my_div b c; my_div b d] in
	    let exists_min_int = List.exists lt_min32 prod_cart64 in
	    let exists_max_int = List.exists gt_max32 prod_cart64 in
	    let min32 = List.fold_right min prod_cart32 Int32.max_int in
	    let max32 = List.fold_right max prod_cart32 Int32.min_int in
	      match_val_bounds exists_min_int exists_max_int min32 max32
	  end
    | _ -> Top

let rem x y =
  match x, y with
    | Val (a, b), Val (c, d) ->
	if contains_zero y then
	  failwith "oulala c'est pas cool non plus"
	else
	  begin
	    let my_rem x y = Int64.rem (Int64.of_int32 x) (Int64.of_int32 y) in
	    let prod_cart32 = [Int32.rem a c; Int32.rem a d; Int32.rem b c; Int32.rem b d] in
	    let prod_cart64 = [my_rem a c; my_rem a d; my_rem b c; my_rem b d] in
	    let exists_min_int = List.exists lt_min32 prod_cart64 in
	    let exists_max_int = List.exists gt_max32 prod_cart64 in
	    let min32 = List.fold_right min prod_cart32 Int32.max_int in
	    let max32 = List.fold_right max prod_cart32 Int32.min_int in
	      match_val_bounds exists_min_int exists_max_int min32 max32
	  end
    | _ -> Top

(* is_safe_val : t -> bool *)
let is_safe_binop ?is_safe_val:(fun _ -> true) op32 op64 x y =
  match (x, y) with
    | Val (a, b), Val (c, d) ->
	let to_64 x32 y32 = op64 (Int64.of_int32 x32) (Int64.of_int32 y32) in
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

	  
let guard op c x =
  match c, x with
    | Val (a, b), Val (c, d) ->
	begin match op with
	  | LTE ->
	      if gt b d then raise EmptySet
	      else Val (max b c, d)
	  | EQ ->
	      if contains x c then c else raise EmptySet
	  | GT ->
	      if lt a c then raise EmptySet
	      else Val (c, min (Int32.add a Int32.one) d)
	  | LT ->
	      if gte b d then raise EmptySet
	      else Val (max (Int32.add b Int32.one) c, d)
	  | NEQ ->
	      ??
	  | GTE ->
	      if lte a c then raise EmptySet
	      else Val (c, min a d)
	end
    | _ -> x
