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
      
End Ops. 