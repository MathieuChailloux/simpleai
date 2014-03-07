module I = Interval
module P = Parity

type t = I.t * P.t

let universe = I.universe, P.universe

let to_string (i, p) = Printf.sprintf "(%s, %s)" (I.to_string i) (P.to_string p)

let singleton i32 = I.singleton i32, P.singleton i32

let of_bounds b = I.of_bounds b, P.of_bounds b

let contains (i1, p1) (i2, p2) =
  I.contains i1 i2 && P.contains p1 p2

let implies ((i, p), cmp, i32) =
  I.implies (i, cmp, i32) && P.implies (p, cmp, i32)

let reduce (i, p) =
  match (i, p) with
  | _, P.Top -> (i, p)
  | I.Val (a, b), _ ->
    let a = if P.singleton a <> p then Int32.add a Int32.one else a in
    let b = if P.singleton b <> p then Int32.sub b Int32.one else b in
    I.Val (a, b), p
  | _ -> (i, p)

let join (i1, p1) (i2, p2) = reduce (I.join i1 i2, P.join p1 p2)
let widen (i1, p1) (i2, p2) = reduce (I.widen i1 i2, P.widen p1 p2)


let neg (i, p) = reduce (I.neg i, P.neg p)

let add (i1, p1) (i2, p2) =
  reduce (I.add i1 i2, P.add p1 p2)
let sub (i1, p1) (i2, p2) = 
  reduce (I.sub i1 i2, P.sub p1 p2)
let mul (i1, p1) (i2, p2) = 
  reduce (I.mul i1 i2, P.mul p1 p2)
let div (i1, p1) (i2, p2) = reduce (I.div i1 i2, P.div p1 p2)
let rem (i1, p1) (i2, p2) = reduce (I.rem i1 i2, P.rem p1 p2)

let is_safe_f f (i1, _) (i2, _) = f i1 i2
let is_safe_add = is_safe_f I.is_safe_add
let is_safe_sub = is_safe_f I.is_safe_sub
let is_safe_mul = is_safe_f I.is_safe_mul
let is_safe_div = is_safe_f I.is_safe_div
let is_safe_mod = is_safe_f I.is_safe_mod

let guard bop (i1, p1) (i2, p2) = reduce (I.guard bop i1 i2, P.guard bop p1 p2)

