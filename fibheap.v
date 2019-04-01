Require Import Orders. 

(**** Aliases ****)
Definition dlink {A: Type} := @list A. (* "Doubly Linked List". *)
Definition dmerge {A: Type} := @app A. 
Definition dsingle {A: Type} (x: A) := cons x nil. 
Definition dempty {A: Type} := @nil A. 
Definition dlength {A: Type} := @length A. 
Definition dmin {A: Type} (d : @dlink A) := (* TO DO *)
  match d with
  | nil => None
  | cons hd tl => Some hd
  end.
Definition drest {A: Type} (d: @dlink A) : @dlink A := (* TO DO *)
  (* Removes the minimum element, and returns the rest of the dlink. *)
  @nil A. 
Definition dconsolidate {A N: Type} (* TO DO *)
           (key: A -> N) (link: A -> A -> A) (d: @dlink A): @dlink A :=
  (* A generic consolidation function. See the `consolidate` procedure of CLRS. *)
  dempty. 



(**************** Definition ****************)
Module Ops (X: OrderedType).
  Definition lt (a b: X.t) : bool :=
    match X.compare a b with
    | Eq => false
    | Lt => true
    | Gt => false
    end.
  Local Notation "a < b" := (lt a b). 

  (* Definition of a Fibonacci Heap. Notable aspects
     - There is no "Node" type. Nodes are themselves fheaps. *)
  Inductive fheap :=
  | Leaf : fheap 
  | Atop : X.t -> fheap -> fheap
  | Ptr : @dlink fheap -> fheap.

  (**** Helpers ****)
  Definition extractdl (H : fheap) : (@dlink fheap) :=
    match H with
    | Leaf => dempty
    | Atop x _ => dsingle H
    | Ptr d => d
    end.

  Definition singleton (x: X.t) :=
    Atop x Leaf.
    
  Definition top (H : fheap) :=
    match H with
    | Leaf => None
    | Atop x _ => Some x
    | Ptr _ => None
    end.
  
  Definition degree (H : fheap) : nat :=
    match H with
    | Leaf => 0
    | Atop x H' =>
      match H' with
      | Leaf => 0
      | _ => 1
      end
    | Ptr d =>
      dlength d
    end.

  Definition minimum_t (H: fheap) : option X.t :=
    (* "Minimum temporary". Needed as a helper function, but is also one of the
       core operations of an fheap. Identical to `minimum` as of Sun Apr  7 23:28:54
       EDT 2019 *)
    match H with
    | Leaf => None
    | Atop x _ => Some x
    | Ptr d =>
      match (dmin d) with
      | None => None (* Should not happen *)
      | Some H' => top H'
      end
    end.

  Definition link (H1 H2: fheap) : fheap :=
    (* The `fib-heap-link` procedure of CLRS. Links two fheaps constructed using
    `Atop`. *)
    match H1, H2 with
    | Atop x1 H1', Atop x2 H2' =>
      if (x1 < x2) then
        Atop x1 (Ptr (dmerge
                        (extractdl H1')
                        (extractdl H2)))
      else
        Atop x2 (Ptr (dmerge
                        (extractdl H1)
                        (extractdl H2')))
    | _, _ => Leaf (* Should not happen *)
    end. 

  Definition consolidate (H: fheap) : fheap :=
    (* The `consolidate` procedure of CLRS. To achieve the required amortized
    time bounds, needs to run in time linear to the number of nodes in the root list. *)
    Ptr (dconsolidate degree link (extractdl H)). 
      

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

  Definition make_heap := Leaf. 

  Fixpoint union (H1 H2: fheap) : fheap :=
    match H1, H2 with
    | Leaf, _ => H2
    | _, Leaf => H1 (* I believe these are necessary for efficiency reasons --
                       so we don't get long pointers of leaves *)      
    | _, _ => Ptr (dmerge (extractdl H1) (extractdl H2))
    end. 
      
  Definition insert (x: X.t) (H: fheap) : fheap :=
    union (singleton x) H.

  Definition minimum : fheap -> option X.t := minimum_t. 

  (* Unlike imperative implementations, doesn't return the minimum
  element. Rather, returns the fheap with the element removed. *)
  Definition extract_min (H: fheap) : option fheap :=
    match H with
    | Leaf => None
    | Atop _ H' => Some H'
    | Ptr d =>
      match (dmin d) with
      | None => None (* Should not happen *)
      | Some H' =>
        match H' with
        | Leaf => None (* Should not happen *)
        | Ptr _ => None (* Should not happen *)
        | Atop x H'' => Some (consolidate (union H'' (Ptr (drest d))))
        end
      end
    end.
      
    

  


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