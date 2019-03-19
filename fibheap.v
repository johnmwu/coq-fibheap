(**** Aliases ****)
(* For ease of changing later. *)
Definition OT := nat. (* "Ordered Type" *)
Definition lt := Nat.ltb. (* "Less than". Assumed to return bool *)
Definition leaf_min := 0. (* The "min" returned when a leaf is put in. *)





(**************** Definition ****************)

(* Define a mergeable heap data structure. Analogous to 'tree' in *)
(* MSetGenTree. *) 
Inductive mheap {X: Type} :=
| Leaf : mheap
| Node : OT -> X -> mheap -> mheap
  (* Take any mheap and put a node on top *)
| Cons : mheap -> mheap -> mheap.
  (* Put two mheaps side by side. Used to create lists of mheaps, which end with *)
  (* a Leaf. *)

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