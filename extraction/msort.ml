
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val div_conq :
    ('a1 list -> 'a1 list * 'a1 list) -> 'a2 -> ('a1 -> 'a2) -> ('a1 list ->
    'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec div_conq splitF x x0 x1 ls =
  let s = (<=) (Pervasives.succ (Pervasives.succ 0)) (length ls) in
  if s
  then let h0 = div_conq splitF x x0 x1 (snd (splitF ls)) in
       x1 ls (div_conq splitF x x0 x1 (fst (splitF ls))) h0
  else (match ls with
        | [] -> x
        | a :: x2 ->
          (match x2 with
           | [] -> x0 a
           | a0 :: x3 ->
             x1 (a :: (a0 :: x3))
               (div_conq splitF x x0 x1 (fst (splitF (a :: (a0 :: x3)))))
               (div_conq splitF x x0 x1 (snd (splitF (a :: (a0 :: x3)))))))

(** val split : 'a1 list -> 'a1 list * 'a1 list **)

let rec split = function
| [] -> ([], [])
| h1 :: l ->
  (match l with
   | [] -> ((h1 :: []), [])
   | h2 :: ls' -> let (ls1, ls2) = split ls' in ((h1 :: ls1), (h2 :: ls2)))

(** val div_conq_split :
    'a2 -> ('a1 -> 'a2) -> ('a1 list -> 'a2 -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let div_conq_split x =
  div_conq split x

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

(** val merge_prog : int list -> int list -> int list -> int list **)

let merge_prog _ =
  merge

(** val msort_prog : int list -> int list **)

let msort_prog =
  div_conq_split [] (fun a -> a :: []) merge_prog
