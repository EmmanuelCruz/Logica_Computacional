
and(true,true):-!.
and(not(false),true):-!.
and(not(false),not(false)):-!.
and(true,not(false)):-!.
and(and(not(true),true),true):-!.

not(false).
not(and(not(X),Y)):- X==true;X==false;Y==true;Y==false.

% PRIMERA VERSION DE CIRCUITO 1
%circuito(X,Y):-and(and(not(X),Y),Y).

% SEGUNDA VERSION DE CIRCUITO 1
circuito(X,Y):-(X==true;not(Y)),Y==true,!.

% PRIMERA VERSION DE CIRCUITO 2
%circuitoDos(X,Y,Z):-not(and(not(X),X)),and(Y,Z),!.

% SEGUNDA VERSION DE CIRCUITO 2
circuitoDos(X,Y,Z):-(X==true;X==false),Y==true,Z==true,!.