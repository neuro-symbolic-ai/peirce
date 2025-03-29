grandparent(X, Y) :- mother(X, Z), mother(Z, Y).
grandparent(X, Y) :- father(X, Z), mother(Z, Y).
grandparent(X, Y) :- mother(X, Z), father(Z, Y).
grandparent(X, Y) :- father(X, Z), father(Z, Y).
