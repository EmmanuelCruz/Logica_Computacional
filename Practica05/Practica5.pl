%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% EJERCICIO 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Push
push(X,L,[X|L]).

% Pop
pop([X|XS],XS):-X=X.

% Append
append([],X,X).
append([X|XS],Y,[X|Z]):-append(XS,Y,Z).

% ListSum
listSum([],0).
listSum([X|XS],S):-listSum(XS,Y),add(X,Y,S).

% Suma
add(X,Y,Z):-Z is X+Y.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% EJERCICIO 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Estados
state(1).
state(2).
state(3).

% Estado Final
finalState(3).

% Alfabeto
elem(a).
elem(b).

% Transiciones
transition(1,b,2).
transition(2,a,2).
transition(2,a,3).
transition(3,b,2).

% Aceptación
aceptation([],Q):-finalState(Q).
aceptation([X|XS],Q):- transition(Q,X,W), aceptation(XS,W),!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% EJERCICIO 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Representación del etado de tablero.
state(on(c,on(b,on(a,void))),void,void).

% Mueve un cubo de posición.
move(state(on(X,Y),void,void),N):-N=state(Y,on(X,void),void),!.
move(state(on(X,Y),Z,void),N):-N=state(Y,Z,on(X,void)),!.
move(state(on(X,void),on(Y,void),on(Z,void)),N):-N=state(void,on(Y,void),on(X,on(Z,void))),!.
move(state(void,on(X,void),on(Y,Z)),N):-N=state(void,void,on(X,on(Y,Z))),!.
move(state(on(X,Y),on(Z,W),void),N):-N=state(Y,on(Z,W),on(void,X)),!.

move(state(on(X,Y),Z,W), N):- N=state(Y,on(X,Z),W),!.
move(state(X,on(Z,Y),W), N):- N=state(X,Y,on(Z,W)),!.
move(state(void,void,X), N):- N=state(void,void,X),!.
move(state(X,Y,Z), N):- N=state(void,on(X,Y),Z),!.
move(state(void,X,Y), N):- N=state(void,void,on(X,Y)),!.

% Path
path(FS,FS,L):-push(FS,[],L),!.
path(IS,FS,L):-move(IS,H),push(IS,[],R),path(H,FS,M),append(R,M,L),!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% PRUEBAS PARA EJERCICIO 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% path(state(on(a,void),on(c,on(b,void)),void),state(void,on(b,void),on(c,on(a, void))),X). %%%
%%% path(state(on(a,void),on(b,void),void),state(void,void,on(b,on(a, void))),X). %%%
%%% path(state(on(a, void), void, void),state(void, void, on(a, void)), X). %%%
%%% path(state(on(c,on(b,on(a,void))),void,void),state(void,void,on(c,on(a,on(b, void)))),X). %%%