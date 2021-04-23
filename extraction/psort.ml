
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val div_conq_pair :
    'a2 -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 list ->
    'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec div_conq_pair x x0 x1 x2 = function
| [] -> x
| a :: x3 ->
  (match x3 with
   | [] -> x0 a
   | a0 :: x4 -> x2 a a0 x4 (x1 a a0) (div_conq_pair x x0 x1 x2 x4))

(** val merge : int list -> int list -> int list **)

let rec merge l1 l2 =
  let rec merge_aux l3 =
    match l1 with
    | [] -> l3
    | a1 :: l1' ->
      (match l3 with
       | [] -> l1
       | a2 :: l2' ->
         if (<=) a1 a2 then a1 :: (merge l1' l3) else a2 :: (merge_aux l2'))
  in merge_aux l2

(** val pair_merge_prog :
    int -> int -> int list -> int list -> int list -> int list **)

let pair_merge_prog _ _ _ l' l'0 =
  merge l'0 l'

(** val psort_prog : int list -> int list **)

let psort_prog =
  div_conq_pair [] (fun a -> a :: []) (fun a1 a2 ->
    let s = (<=) a1 a2 in if s then a1 :: (a2 :: []) else a2 :: (a1 :: []))
    (fun a1 a2 l h h0 -> pair_merge_prog a1 a2 l h0 h)
