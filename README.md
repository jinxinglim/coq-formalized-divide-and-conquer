# Induction-Principles-to-Sorting-Algorithms (INCOMPLETE)

> **NOTE:** This branch does not require installation of CoqHammer. Hence, most of the codes are not automated. As a result, they are longer than the ones in main-hammer branch.

This respository contains the formalization of different variations of divide-and-conquer algorithm design paradigm for lists, which lead to different sorting algorithms. All the sorting algorithms are proven in a top-down approach from the type:
```coq
Theorem sort_prog : forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
```
The different variations of proofs of the above type, which lead to different sorting algorithms, are extracted as OCaml programs and are stored in the "extraction"
folder.

The following are the Coq files in the "theories" folder:
1. DivConq.v: contains the formalization of different variations of divide-and-conquer algorithm design paradigm for lists, which are derived from well-founded induction. The following are the different variations:
    
    a. div_conq_split:
    ```coq
    forall (A : Type) (P : list A -> Type),
    P [::]
    -> (forall a : A, P [a])
    -> (forall  ls : list A, P (fst (split A ls)) -> P (snd(split A ls)) -> P ls)
    -> forall  ls : list A, P ls
    ```
    where the split function is defined as follows:
    ```coq
    Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' => let (ls1, ls2) := split ls' in
        (h1 :: ls1, h2 :: ls2)
    end.
    ```

    b. div_conq_pair
    ```coq
    forall (A : Type) (P : list A -> Type),
    P [::]
    -> (forall a : A, P [a])
    -> (forall  a1 a2 : A, P [:: a1; a2])
    -> (forall (a1 a2 : A) (l : list A), P [:: a1; a2] -> P l -> P (a1 :: a2 :: l))
    -> forall l : list A, P l
    ```

    c. div_conq_pivot
    ```coq
    forall (A : Type) (P : list A -> Type),
    P [::]
    -> (forall (a : A) (l : list A), P (fst (split_pivot al))-> P (snd (split_pivot a l)) -> P (a :: l))
    -> forall l : list A, P l
    ```
    where split_pivot is defined as follows:
    ```coq
    Fixpoint split_pivot (pivot : A) l : list A * list A :=
    match l with
    | nil => (nil, nil)
    | a :: l' => let (l1, l2) := (split_pivot pivot l') in
        if le_dec a pivot 
        then (a :: l1, l2) else (l1, a :: l2)
    end.
    ```

2. isort.v: contains proof by induction, which leads to insertion sort.
3. msort.v: contains proof by div_conq_split, which leads to merge sort.
4. psort.v: contains proof by div_conq_pair, which leads to pair sort (similar to insertion sort, just that instead of cutting 1 element at a time, this program cuts two elements at a time)
5. qsort.v: contains proof by div_conq_pivot, which leads to quick sort.

## Prerequitses

Coq Version 8.12

## Make and compile all files

1. Go to the "Induction-Principles-to-Sorting-Algorithms" folder.
2. Run the Makefile in terminal with the following command:
    ```
    $ make
    ```
3. To test the extracted files, run the following command in terminal:
    ```
    $ make test_extraction
    ```
