
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val sort_cons_prog : int -> int list -> int list -> int list **)

let rec sort_cons_prog a _ = function
| [] -> a :: []
| y :: l ->
  let s = sort_cons_prog a l l in
  let s0 = (<=) a y in if s0 then a :: (y :: l) else y :: s

(** val insert_prog : int -> int list -> int list **)

let insert_prog a l =
  sort_cons_prog a l l
