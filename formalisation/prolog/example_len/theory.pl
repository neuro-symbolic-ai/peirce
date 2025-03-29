f(L, H) :- head(L, H).
f(L, H) :- tail(L, T), f(T, H1), H is H1 + 1.
