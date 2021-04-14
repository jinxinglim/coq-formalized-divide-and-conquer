
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val sort_cons_prog : int -> int list -> int list -> int list **)

let rec sort_cons_prog a _ = function
| [] -> a :: []
| y :: l ->
  let s = sort_cons_prog a l l in
  let s0 = (<=) a y in if s0 then a :: (y :: l) else y :: s

(** val isort_prog : int list -> int list **)

let rec isort_prog = function
| [] -> []
| y :: l0 -> sort_cons_prog y l0 (isort_prog l0)
