
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
