module Make (Val : UnrelState.Data) =
struct
  
  type t = Val.t * Val.t

  (* m and p refer to main and pilot values *)
  let to_string (m, p) =
    Printf.sprintf "(main = %s , pilot = %s)" (Val.to_string m) (Val.to_string p)

  let universe = Val.universe, Val.universe

  let singleton i = Val.singleton i, Val.singleton i

  let of_bounds x = Val.of_bounds x, Val.of_bounds x

  let contains (m1, p1) (m2, p2) =
    (Val.contains m1 m2 && m1 <> m2)
    || (m1 = m2 && Val.contains p1 p2)

  let join (m1, p1) (m2, p2) = Val.join m1 m2, Val.join p1 p2

  let widen (m1, p1) (m2, p2) =
    let res =
      if contains (m1, p1) (m2, p2) then
	(m1, p1)
      else if Val.contains p1 p2 then
	let res = (p2, p2) in
	Printf.printf "Stabilized value = %s\n" (Val.to_string p2);
	res
      else
	(Val.join m1 m2, Val.widen p1 p2)
    in
    (*Printf.printf "Lookahead widening %s\nand %s\n= %s\n" (to_string (m1, p1)) (to_string (m2, p2)) (to_string res);*)
    res

  let implies ((_, p), op, i) = Val.implies (p, op, i)

  let neg (m, p) = Val.neg m, Val.neg p

  let pair_map f (m1, p1) (m2, p2) = f m1 m2, f p1 p2

  let add = pair_map Val.add
  let sub = pair_map Val.sub
  let mul = pair_map Val.mul
  let div = pair_map Val.div
  let rem = pair_map Val.rem

  let is_safe_f f (m1, p1) (m2, p2) = f m1 m2 && f p1 p2

  let is_safe_add = is_safe_f Val.is_safe_add
  let is_safe_sub = is_safe_f Val.is_safe_sub
  let is_safe_mul = is_safe_f Val.is_safe_mul
  let is_safe_div = is_safe_f Val.is_safe_div
  let is_safe_mod = is_safe_f Val.is_safe_mod

  let guard bop = pair_map (Val.guard bop)

end
