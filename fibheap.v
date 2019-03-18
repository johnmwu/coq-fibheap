(**************** Definition ****************)

(* Define a mergeable heap data structure. Analogous to 'tree' in *)
(* MSetGenTree. *) 
Inductive mheap {X: Type} :=
| Leaf : mheap
| Node : nat -> X -> mheap -> mheap
  (* Take any mheap and put a node on top *)
| Cons : mheap -> mheap -> mheap.
  (* Put two mheaps side by side *)

(* Alternative Mon Mar 18 00:13:09 EDT 2019 *)
(* "doubly linked list". As of Mon Mar 18 00:21:36 EDT 2019, unclear how to *)
(* implement. Should, for example, support unions in constant time *)
(* Definition doublell := list.  *)

(* Inductive mheap (X: Type) := *)
(* | Leaf : mheap X *)
(* | Node : nat -> X -> nheap X -> mheap X *)
(* where nheap (X: Type) := doublell (mheap X).  *)

(* Alternative Mon Mar 18 00:57:23 EDT 2019 *)
(* Inductive mheap (X: Type) := *)
(* | Leaf : mheap X *)
(* | Node : nat -> X -> mheap X -> mheap X *)
(* | Ptr : doublell (mheap X) -> mheap X.  *)


(**************** Helper functions ****************)
Definition singleton {X: Type} (x: X) (n: nat) :=
  Node n x Leaf. 



(**************** Mergeable heap operations ****************)
(* As defined in CLRS, a mergeable heap has 5 fundamental operations:
   * Make-heap()
   * Insert(H, x)
   * Minimum(H)
   * Extract-min(H)
   * Union(H1, H2)
   In addition, their implementation of a fibonacci heap has two additional *)
(* operations:
   * Decrease-key(H, x, k)
   * Delete(H, x) *)
Definition insert {X: Type} (x: X) (n: nat) (H: mheap) :=
  match H with
  | Leaf => singleton x n
  | Node n0 _ _ =>
    if (Nat.ltb n n0) then
      Cons (singleton x n) H
    else
      Cons H (singleton x n)
  | Cons H1 H2 =>
    match H1 with
    | Leaf => Cons (singleton x n) H2
    | Node n0 _ _ =>
      if (Nat.ltb n n0) then
        Cons (singleton x n) H
      else
        Cons H1 (Cons (singleton x n) H2)
    | Cons _ _ => Cons (singleton x n) H (* This case should not happen *)
    end
  end. 
      
Definition union {X: Type} (H1: mheap X) (H2: mheap X) :=
  match H1, H2 with
  | Leaf, _ => H2
  | _, Leaf => H1
  | Node