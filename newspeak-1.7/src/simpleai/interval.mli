type t = Top | Val of Int32.t * Int32.t

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
val guard: UnrelState.bop -> t -> t -> t
val to_string: t -> string
