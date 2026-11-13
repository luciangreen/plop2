% Text built from fixed parts and an input.
greet(Name, Out) :-
    append("Hello, ", Name, T),
    append(T, "!", Out).

% Each input character twice: char K of the output is input char (K+1)//2.
double([], []).
double([X|Xs], [X, X|Ys]) :- double(Xs, Ys).

% Reversal: char K needs the whole input (its length).
backwards(In, Out) :- reverse(In, Out).

% Computes on character values: the symbolic run cannot decide it.
shout(In, Out) :- maplist(up, In, Out).
up(C, U) :- upcase_atom(C, U).

% A cut: detlog2 turns it into if_commit/3 before slicing.
tag(In, Out) :- In = [], !, Out = "empty".
tag(In, Out) :- append("<", In, T), append(T, ">", Out).
