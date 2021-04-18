Require Import List.

Require Import Bool.

Require Import ZArith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Parameters (A:Type)
           (a b x:A)
           (l l1 l2 : list A).


(* Razonamiento sobre la funcion elem *)

Fixpoint elem (x:A) (l: list A)  :=
 match l with 
  | nil => False
  | (b::bs) => x = b \/ elem x bs
 end.

Theorem elem_eq : elem a (a :: l).
Proof.
intros.
simpl.
left.
trivial.
Qed.


Theorem elem_nil : forall a:A, ~ elem a nil.
Proof.
intros.
simpl.
unfold not.
intros.
trivial.
Qed.


Theorem elem_cons : elem b l -> elem b (a :: l).
Proof.
intros.
simpl.
right.
trivial.
Qed.

Fixpoint longitud (l : list A) : nat :=
 match l with
   | nil => 0
   | (x::ls) => S(longitud (ls))
 end.

Theorem longConc : longitud (l1++l2) = longitud (l1) + longitud l2.
Proof.
induction l1.
simpl.
reflexivity.
simpl.
rewrite IHl0.
reflexivity.
Qed.


