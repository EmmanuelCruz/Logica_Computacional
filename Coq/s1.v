Parameters (b z c d q t p r:Prop)
           (A:Type)
           (P Q: A -> Prop)
           (R : A -> A -> Prop).

 
Theorem Argumento1: (b /\ z) /\ (z -> c /\ d) /\ (c /\ b -> q) -> q \/t.
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
left. 
apply H3.
split.
destruct H1 as [H4 H5].
assert (c/\d).
apply H2.
trivial.
destruct H.
trivial.
destruct H1.
trivial.
Qed.

Print Argumento1.


Theorem Argumento2: p \/ (q /\ r) -> (p \/ q) /\ ( p \/ r).
Proof.
intro.
split.
destruct H.
left.
trivial.
destruct H.
right.
trivial.
destruct H.
left.
trivial.
right.
destruct H.
trivial.
Qed.

Theorem ex1: (forall x, P x) \/ (forall y, Q y) -> (forall x, P x \/ Q x).
Proof.
intros.
destruct H.
left.
apply H.
right.
apply H.
Qed.


Theorem Argum1: (forall y:A, P y -> Q y) -> (forall x:A, (exists y:A, P y /\ R x y) -> exists z:A, Q z /\ R x z).
Proof.
intro.
intro.
intro.
destruct H0 as [b]. (* Reemplazamos y por un elemento, digamos b. Puedo usar b porque la definimos al inicio del archivo. *)
destruct H0 as [H1 H2].
exists b. (*Afirmo que quien existe es b*)
split.
apply H. (* Éste en realidad son dos apply consecutivos, uno para forall y otro para la implicación *)
trivial.
trivial.
Qed.
