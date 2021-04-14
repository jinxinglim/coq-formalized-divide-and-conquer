# Induction-Principles-to-Sorting-Algorithms

This respository contains the following files:
1. DivConq.v: contains the formalization of different variations of divide-and-conquer algorithm design paradigm for lists, which are derived from well-founded induction.
    a. div_conq_split:
    ```
    forall (A : Type) (P : list A -> Type),
    P [::]
    -> (forall a : A, P [a])
    -> (forall  ls : list A, P (fst (split A ls)) -> P (snd(split A ls)) -> P ls)
    -> forall  ls : list A, P ls
    ```

    b.
    
## Prerequitses

1. Coq Version 8.12
2. CoqHammer
    Just need to install coq-hammer-tactics:
    ```
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-hammer-tactics
    ```

## Make and compile all files

1. Go to the "Induction-Principles-to-Sorting-Algorithms" folder.
2. Run the Makefile in terminal with the following command:
    ```
    make
    ```
3. To test the extracted files, run the following command in terminal:
    ```
    make test_extraction
    ```
