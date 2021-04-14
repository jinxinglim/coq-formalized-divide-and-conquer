open Isort
open Insert
open Msort
open Merge
open Psort
open Qsort
open Printf
open Random


let print_list = function
  | [] -> print_string "[]"
  | h :: t ->
    print_string "["; print_int h;
    let rec print_tail = function
      | [] -> print_string "]"
      | x :: xs -> print_string "; "; print_int x; print_tail xs in
    print_tail t
    

let time f =
  let t = Unix.gettimeofday () in
  let res = f () in
  printf "Execution time: %f seconds" (Unix.gettimeofday () -. t);
  ignore(res)


let rand_select list n =
    let rec extract acc n = function
      | [] -> raise Not_found
      | h :: t -> if n = 0 then (h, acc @ t) else extract (h::acc) (n-1) t
    in
    let extract_rand list len =
      extract [] (Random.int len) list
    in
    let rec aux n acc list len =
      if n = 0 then acc else
        let picked, rest = extract_rand list len in
        aux (n-1) (picked :: acc) rest (len-1)
    in
    let len = List.length list in
    aux (min n len) [] list len


let rand_select_replace list n =
    let rec extract acc n = function
      | [] -> raise Not_found
      | h :: t -> if n = 0 then (h, acc @ t) else extract (h::acc) (n-1) t
    in
    let extract_rand list len =
      extract [] (Random.int len) list
    in
    let rec aux n acc list len =
      if n = 0 then acc else
        let picked, rest = extract_rand list len in
        aux (n-1) (picked :: acc) list len
    in
    let len = List.length list in
    aux n [] list len


let range a b =
    let rec aux a b =
      if a > b then [] else a :: aux (a+1) b  in
    if a > b then List.rev (aux b a) else aux a b


let lotto_select_replace n m = rand_select_replace (range 1 m) n


let lotto_select n m = rand_select (range 1 m) n
  

let () =
  let l = lotto_select 100 500 in
    print_string "Original list:\n"; 
    print_list l; print_newline ();
    let l1 = isort_prog l in
    print_string "Insertion sorted:\n"; 
    print_list l1; print_newline ();
    time (fun () -> isort_prog l); print_newline ();
    let l2 = insert_prog 41 l1 in
    print_string "Insert 41 into sorted version of l:\n"; 
    print_list l2; print_newline ();
    time (fun () -> insert_prog 41 l1); print_newline ();
    let l3 = insert_prog 41 l in
    print_string "Insert 41 into unsorted version of l:\n"; 
    print_list l3; print_newline ();
    time (fun () -> insert_prog 41 l); print_newline ();
    let l4 = msort_prog l in
    print_string "Merge sorted:\n"; 
    print_list l4; print_newline ();
    time (fun () -> msort_prog l); print_newline ();
    let l5 = merge [4;3;7;4;9;1;2;6;44] l in
    print_string "Merge [4;3;7;4;9;1;2;6;44] into original list:\n"; 
    print_list l5; print_newline ();
    time (fun () -> merge [4;3;7;4;9;1;2;6;4] l); print_newline ();
    let l6 = psort_prog l in
    print_string "Pair sorted:\n"; 
    print_list l6; print_newline ();
    time (fun () -> psort_prog l); print_newline ();
    let l7 = qsort_prog l in
    print_string "Quick sorted:\n"; 
    print_list l7; print_newline ();
    time (fun () -> qsort_prog l); print_newline ();