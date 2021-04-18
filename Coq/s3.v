Variables p q r s t x l m:Prop.

Theorem negacion: p -> ~~p.
Proof.
intro.
unfold not.
intro.
apply H0.
trivial.
Qed.


Theorem NegImp: (p -> q) -> (p -> ~q) -> ~p.
Proof.
intros.
unfold not.
intro.
unfold not in H0.
assert (q -> False).
apply H0.
trivial.
apply H2.
apply H.
trivial.
Qed.

Theorem NegImpConj: p /\ ~q -> ~(p -> q).
Proof.
intro.
unfold not.
intro.
destruct H.
assert q.
apply H0.
trivial.
apply H1.  (* Obsérvese que no hay necesidad de desdoblar la definición de ~*)
trivial.
Qed.

Theorem dmorganO : ~ ( p \/ q ) <-> ~p /\ ~q.
Proof.
unfold iff.
split.
unfold not.
intro.
split.
intro.
apply H.
left.
assumption.

intro.
apply H.
right.
assumption.

unfold not.
intros.
destruct H.
destruct H0.
apply H.
assumption.
apply H1.
assumption.
Qed.


Theorem ExFalso: False -> p.
Proof.
intros.
elim H. 
Qed.

Theorem texcimp: (p \/ ~p) -> ~~p -> p.
Proof.
intros.
destruct H.
trivial.
apply ExFalso.
apply H0.
trivial.
Qed.

Theorem SilogismoDisy: (p \/ q) /\ ~p -> q.
Proof.
intro.
destruct H.
destruct H.
absurd (p).
trivial.
trivial.
trivial.
Qed.


Theorem Contrapositiva: (p -> q) -> (~q -> ~p).
Proof.
intros.
unfold not.
intro.
apply H0.
apply H.
trivial.
Qed.

Require Import Classical.

Check classic.

Check classic r.

Check classic (p /\ q -> r).

Check NNPP.

Check NNPP (p /\ q -> r).

Theorem edn: ~~p <-> p.
Proof.
unfold iff.
split.
exact (NNPP p).
intro.
unfold not.
intro.
apply H0.
trivial.
Qed.


Theorem DefImp: (p -> q) <-> ~p \/ q.
Proof. 
unfold iff.
split.
intro.
assert (p \/ ~p).
exact (classic p).
destruct H0.
right.
apply H.
trivial.
left.
trivial.
intros.
destruct H.
absurd p.
trivial.
trivial.
trivial.
Qed.

Theorem ContraPos: (p -> q) <-> (~q -> ~p).
Proof.
unfold iff.
split.
intros.
assert (p \/ ~p).
exact (classic p).
destruct H1.
absurd (q).
trivial.
apply H.
trivial.
trivial.
intros.
assert (q \/ ~q).
exact (classic q).
destruct H1.
trivial.
absurd (p).
apply H.
trivial.
trivial.
Qed.

Theorem TEDebil: ((p -> q) -> q) \/ (p->q).
Proof.
assert ((p->q) \/ ~(p->q)).
exact (classic (p->q)).
destruct H.
right.
trivial.
left.
intro.
absurd (p->q).
trivial.
trivial.
Qed.



