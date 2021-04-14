
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val div_conq_pair :
  'a2 -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 list ->
  'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val merge : int list -> int list -> int list

val pair_merge_prog :
  int -> int -> int list -> int list -> int list -> int list

val psort_prog : int list -> int list
