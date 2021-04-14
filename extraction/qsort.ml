
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec =
  (<=)

(** val le_dec : int -> int -> bool **)

let le_dec =
  le_gt_dec

(** val split_pivot :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list * 'a1 list **)

let rec split_pivot le_dec0 pivot = function
| [] -> ([], [])
| a :: l' ->
  let (l1, l2) = split_pivot le_dec0 pivot l' in
  if le_dec0 a pivot then ((a :: l1), l2) else (l1, (a :: l2))

(** val div_conq_pivot :
    ('a1 -> 'a1 -> bool) -> 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2 -> 'a2) ->
    'a1 list -> 'a2 **)

let rec div_conq_pivot le_dec0 x x0 = function
| [] -> x
| a :: x1 ->
  x0 a x1 (div_conq_pivot le_dec0 x x0 (fst (split_pivot le_dec0 a x1)))
    (div_conq_pivot le_dec0 x x0 (snd (split_pivot le_dec0 a x1)))

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

(** val qsort_prog : int list -> int list **)

let qsort_prog =
  div_conq_pivot le_dec [] (fun a _ h h0 -> merge h (a :: h0))
