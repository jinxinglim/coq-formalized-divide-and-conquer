
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val div_conq :
  ('a1 list -> 'a1 list * 'a1 list) -> 'a2 -> ('a1 -> 'a2) -> ('a1 list ->
  'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val split : 'a1 list -> 'a1 list * 'a1 list

val div_conq_split :
  'a2 -> ('a1 -> 'a2) -> ('a1 list -> 'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val merge : int list -> int list -> int list

val merge_prog : int list -> int list -> int list -> int list

val msort_prog : int list -> int list
