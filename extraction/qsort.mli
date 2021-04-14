
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool

val split_pivot :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list * 'a1 list

val div_conq_pivot :
  ('a1 -> 'a1 -> bool) -> 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2 -> 'a2) ->
  'a1 list -> 'a2

val merge : int list -> int list -> int list

val qsort_prog : int list -> int list
