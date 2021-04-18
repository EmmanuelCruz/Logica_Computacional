Require Import List.

Require Import Bool.

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
simpl.
left.
reflexivity.
Qed.


Theorem elem_nil : forall a:A, ~ elem a nil.
Proof.
intro.
intro.
simpl in H.
trivial.
Qed.

Theorem elem_conc : forall (a : A) (la lb : list A), elem a (la++lb) -> elem a la \/ elem a lb.
Proof.
intros.
induction la.
right.
simpl in H.
trivial.
simpl.
rewrite or_assoc.
simpl in H.
destruct H.
left.
trivial.
right.
apply IHla.
trivial.
Qed.



Fixpoint longitud (l : list A) : nat :=
 match l with
   | nil => 0
   | (x::ls) => S(longitud (ls))
 end.

Theorem longConc : forall (la lb:list A), longitud(la ++ lb) = longitud (la)+longitud(lb).
Proof.
intros.
induction la.
simpl.
reflexivity.
simpl.
rewrite IHla.
reflexivity.
Qed.

Fixpoint rev (l:list A): list A :=
 match l with
  | nil => nil
  | (x::xs) => rev xs ++ [x]
 end.

Theorem Trev : forall (la : list A), longitud(rev la) = longitud la.
(* Prueba pendiente *)








