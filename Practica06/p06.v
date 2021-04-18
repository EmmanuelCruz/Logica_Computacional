(********************************************************************* 
       Lógica computacional 2018-2
       Práctica 06: Coq- Deducción Natural e Inducción sobre listas.
       Selene Linares  
**********************************************************************

INTEGRANTES DEL EQUIPO

CRUZ HERNÁNDEZ EMMANUEL
MARTÍNEZ HERNÁNDEZ LUIS EDUARDO
MONTES INCIN SARA DORIS

**********************************************************************)

Section DeduccionNatural.

Parameters ( q t p r s w:Prop)
           (A:Type)
           (a b c d e:A)
           (P Q R G F T: A -> Prop).


(****** Deducción Natural Proposicional ******)

Theorem ExFalso: forall (x:Prop), False -> x.
Proof.
intros.
elim H. 
Qed.

Theorem ej1_a : (p -> q) -> (p -> r) -> (q -> r -> t) -> p -> t.
Proof.
Admitted.

(****** EJERCICIO 1A ******)
Theorem ejercicio1a: (p -> q) /\ (r -> s) -> p /\ r -> q /\ s.
Proof.
intros.
split.
destruct H0.
apply H.
trivial.
destruct H0.
apply H.
trivial.
Qed.

(****** EJERCICIO 1B ******)
Theorem ejercicio1b: (p -> q) -> (q -> r) -> ((p -> r) -> t -> q) ->  ((p -> r) -> t) -> q.
Proof.
intros.
apply H1.
intro.
apply H0.
apply H.
trivial.
apply H2.
intro.
apply H0.
apply H.
trivial.
Qed.

(****** EJERCICIO 1C ******)
Theorem ejercicio1c: (p /\ (q -> False)) /\ (p -> (q -> False)) -> ((p -> q) -> False) /\ (q -> (p -> False)).
Proof. 
intros.
destruct H.
split.
intro.
apply H0.
destruct H.
trivial.
apply H1.
destruct H.
trivial.
intros.
destruct H.
apply H3.
trivial.
Qed.

(****** EJERCICIO 1D ******)
Theorem ejercicio1d:  (p /\ q) /\ (r/\ (s -> False)) /\ (q -> p -> t) -> (t -> r -> s \/ w) -> w.
Proof.
intros.
destruct H.
destruct H1.
destruct H1.
destruct H.
assert (p -> t).
apply H2.
trivial.
assert(t).
apply H5.
trivial.
assert(r->s\/w).
apply H0.
trivial.
assert (s\/w).
apply H7.
trivial.
destruct H8.
assert (False).
apply H3.
trivial.
elim H9.
trivial.
Qed.

(****** Deducción Natural Primer Orden *******)

Theorem ej2_a: (exists x, P x \/ exists x, Q x) -> exists x, P x \/ Q x.
Proof.
Admitted.

(****** EJERCICIO 2A ******)
Theorem ejercicio2a: (exists x, P x /\ Q c) /\ (forall x, P x -> R x) -> (Q c /\ (exists x, P x /\ R x)).
Proof.
intros.
destruct H.
split.
destruct H as [b].
destruct H.
trivial.
destruct H as [a].
destruct H.
exists a.
split.
trivial.
apply H0.
trivial.
Qed.

(****** EJERCICIO 2B ******)
Theorem ejercicio2b: (forall x, G x -> P x \/ R x) /\ (forall x, F x -> T x) -> ((forall x, P x \/ R x -> F x) -> (forall x, G x -> T x)).
Proof.
intros.
destruct H.
apply H2.
apply H0.
apply H.
trivial.
Qed.

End DeduccionNatural.

(****** Inducción estructural sobre Listas ********)

Section InduccionListas.

Require Import List.

Require Import Bool.

Require Import ZArith.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Parameters (l l1 l2 : list A).

Fixpoint longitud (l : list A) : nat :=
 match l with
   | nil => 0
   | (x::ls) => S(longitud (ls))
 end.

Theorem longConc : forall (la lb:list A), longitud(la ++ lb) = longitud la + longitud lb.
Proof.
intros.
induction la.
simpl.
reflexivity.
simpl.
rewrite IHla.
reflexivity.
Qed.

(****** EJERCICIO 3A ******)
Fixpoint rev (l:list A): list A :=
 match l with
  | nil => nil
  | (x::xs) => rev(xs) ++ [x]
 end.

(****** EJERCICIO 3B ******)
Theorem ejercicio3b: forall (la:list A), la++nil=la.
Proof.
induction la.
simpl.
reflexivity.
simpl.
rewrite IHla.
reflexivity.
Qed.

(****** EJERCICIO 3C ******)
Theorem ejercicio3c: forall (la lb lc:list A), (la++lb)++lc = la++(lb++lc).
Proof.
intros.
induction la.
simpl.
reflexivity.
simpl.
rewrite IHla.
reflexivity.
Qed.

(****** EJERCICIO 3D ******)
Theorem RevConc : forall (la lb:list A), rev (la++lb) = rev lb ++ rev la.
Proof.
intros.
induction la.
simpl.
rewrite ejercicio3b.
reflexivity.
simpl.
rewrite IHla.
rewrite ejercicio3c.
reflexivity.
Qed.

(****** EJERCICIO EXTRA ******)
Theorem puntoExtra: forall (la:list A), rev(rev(la))=la.
Proof.
intros.
induction la.
simpl.
reflexivity.
simpl rev.
rewrite RevConc.
simpl.
rewrite IHla.
reflexivity.
Qed.


End InduccionListas.


