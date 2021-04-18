hasPhone(g).
door(a,b).
door(b,c).
door(b,e).
door(c,d).
door(d,e).
door(e,g).
door(e,f).

camino(g,g) :- write(g).
camino(X,Y):- hasPhone(Y),X\==Y,door(X,Z),write(X),nl,camino(Z,Y),!.
    
way(g,g) :- write(g).
way(X,Y):- hasPhone(Y),X\==Y,door(X,Z),Z\==d,Z\==f,write(X),nl,way(Z,Y),!.
