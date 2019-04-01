Require Import Orders. 

(**** Aliases ****)
(* For ease of changing later. *)
Definition key_type := nat. (* Type of keys. Needs to be comparable *)
Definition key_lt := Nat.ltb. (* "Less than" for keys. Assumed to return bool *)
Definition val_type := nat. (* Type of values. Can be anything. Will generalize *)
(* eventually *)


Definition leaf_min := 0. (* The "min" returned when a leaf is put in. *)

Module Type DLink (X: OrderedType).
  (* "Doubly linked list". The collection type used in CLRS to make everything
     work. Does not have to be implemented as a doubly linked list. *)
  Parameter t : Type. (* The collection type *)
  Parameter singleton : X.t -> t. (* Single element collection *)
  Parameter merge : t -> t -> t.
  Parameter min : t -> option X.t. 
End DLink.

Module Def (X: OrderedType) <: OrderedType.
  Inductive fheap := 
  | Leaf : fheap 
  | Atop : X.t -> fheap -> fheap (* Put a node atop an existing fheap *)
  | Ptr : dlink.t -> fheap. (* Create an fheap out of a collection of Atops. *)
  

(**************** Definition ****************)

Module Ops (X: OrderedType) (dlink: DLink X).
  
  Inductive fheap := 
  | Leaf : fheap 
  | Atop : X.t -> fheap -> fheap (* Put a node atop an existing fheap *)
  | Ptr : dlink.t -> fheap. (* Create an fheap out of a collection of Atops. *)

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

  (* Comments: 
   - Mon Mar 18 22:51:53 EDT 2019
     - Ideally, there aren't so many "impossible" cases to worry about
   *)

  Fixpoint union (H1 H2: fheap) : fheap :=
    match H1, H2 with
    | Leaf, _ => H2
    | _, Leaf => H1
    | 
    
  

Fixpoint union_helper {X: Type} (H1: mheap X) (H2: mheap X) :=
  match H1, H2 with
  | Leaf, _ => H2
  | _, Leaf => H1
  | Node _ _ _, _ =>
    Cons H1 H2
  | Cons H11 H12, _



  | Node n1 _ _, Node n2 _ _ =>
    if (lt n1 n2) then
      Cons H1 (Cons H2 Leaf)
    else
      Cons H2 (Cons H1 Leaf)
  | Node n1 _ _, Cons H21 H22 =>
    match H21 with
    | Leaf => union_assert_false H1 H2 (* should not happen *)
    | Node n2 _ _ =>
      if (lt n1 n2) then
        Cons H1 H2
      else
        Cons H21 (union H1 H22)
    | Cons _ _ => union_assert_false H1 H2
    end
  | Cons 


(**************** Helpers ****************)
(**** assert_false objects ****)
Definition union_assert_false {X: Type} (H1 H2: @mheap X) :=
  @Leaf X. 
Definition min_assert_false {X: Type} (H: @mheap X) :=
  leaf_min. 

(**** Functions ****)
Definition singleton {X: Type} (x: X) (n: OT) :=
  Node n x Leaf. 
Definition min {X: Type} (H: @mheap X) :=
  match H with
  | Leaf => leaf_min
  | Node n _ _ => n
  | Cons H1 H2 =>
    match H1 with
    | Leaf => min_assert_false H
    | Node n _ _ => n
    | Cons _ _ => min_assert_false H
    end
  end.
    



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

(* Comments: 
   - Mon Mar 18 22:51:53 EDT 2019
     - Ideally, there aren't so many "impossible" cases to worry about
*)
Definition insert {X: Type} (n: OT) (x: X) (H: mheap) :=
  match H with
  | Leaf => singleton x n
  | Node n0 _ _ =>
    if (lt n n0) then
      Cons (singleton x n) (Cons H Leaf)
    else
      Cons H (Cons (singleton x n) Leaf)
  | Cons H1 H2 =>
    match H1 with
    | Leaf => Cons (singleton x n) H2 (* Should not happen *)
    | Node n0 _ _ =>
      if (lt n n0) then
        Cons (singleton x n) H
      else
        Cons H1 (Cons (singleton x n) H2)
    | Cons _ _ => Cons (singleton x n) H (* Should not happen *)
    end
  end. 
      
(* This is similar to appending two lists *)
Fixpoint union_helper {X: Type} (H1: mheap X) (H2: mheap X) :=
  match H1, H2 with
  | Leaf, _ => H2
  | _, Leaf => H1
  | Node _ _ _, _ =>
    Cons H1 H2
  | Cons H11 H12, _



  | Node n1 _ _, Node n2 _ _ =>
    if (lt n1 n2) then
      Cons H1 (Cons H2 Leaf)
    else
      Cons H2 (Cons H1 Leaf)
  | Node n1 _ _, Cons H21 H22 =>
    match H21 with
    | Leaf => union_assert_false H1 H2 (* should not happen *)
    | Node n2 _ _ =>
      if (lt n1 n2) then
        Cons H1 H2
      else
        Cons H21 (union H1 H22)
    | Cons _ _ => union_assert_false H1 H2
    end
  | Cons 