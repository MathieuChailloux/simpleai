type t = Even | Odd | Top

let universe = Top

let singleton =
  let two = Int32.add Int32.one Int32.one in
  fun i32 -> if Int32.rem i32 two = Int32.zero then Even else Odd

let of_bounds (i1, i2) = if i1 = i2 then singleton i1 else Top

let join x y =
  match x, y with
  | Even, Even -> Even
  | Odd, Odd -> Odd
  | _ -> Top

let widen = join

let contains x y =
  match x, y with
  | Top, _ -> true
  | _, Top -> false
  | _ -> x = y

let implies _ = false

let neg = function
  | Odd -> Even | _ -> Top

let add x y =
  match x, y with
  | Even, Even | Odd, Odd -> Even
  | Even, Odd | Odd, Even -> Odd
  | _ -> Top

let sub x y =
  match x, y with
  | Even, Even | Odd, Odd -> Even
  | Even, Odd | Odd, Even -> Odd
  | _ -> Top

let mul x y =
  match x, y with
  | Even, _ | _, Even -> Even
  | Odd, Odd -> Odd
  | _ -> Top

let div _ _ = Top

let rem x y =
  match x, y with
  | Even, Even -> Even
  | Odd, Even -> Even
  | _ -> Top

let is_safe_add _ _ = true
let is_safe_sub _ _ = true
let is_safe_mul _ _ = true
let is_safe_div _ _ = true
let is_safe_mod _ _ = true

let guard op cond x =
  match op, x with
  | UnrelState.EQ, Top -> cond
  | UnrelState.EQ, _ -> if x <> cond then raise UnrelState.Emptyset else x
  | _, Top -> Top
  | _ -> x

let to_string = function
  | Even -> "Pair"
  | Odd -> "Impair"
  | Top -> "?"
