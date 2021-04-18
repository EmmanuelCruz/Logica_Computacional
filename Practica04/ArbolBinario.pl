elem(X,bt(node(A,T1,T2))) :- (elem(X,(T1));elem(X,(T2));X==A).
elem2(X,bt(node(A,T1,T2))) :- (elem2(X,(T1)),elem2(X,(T2));X>A).
elem3(X,bt(node(A,T1,T2))) :- (elem3(X,(T1)),elem3(X,(T2));X<A).
elem4(X,bt(node(A,T1,T2))) :- (elem3(X,(T1));elem3(X,(T2));X==bt(node(A,T1,T2))).