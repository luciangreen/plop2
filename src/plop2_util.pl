/*  plop2_util.pl - small helpers shared by plop2's modules (detlog2's
    term.pl, reader.pl and cut_elim.pl provide the rest).
*/

list_t(Xs, T) :-
    mk_list(Xs, atom('[]'), T).

%  static_list(+Term, -Maybe): the elements of a literal list term.
static_list(T, M) :-
    if_commit(T == atom('[]'),
              M = just([]),
              if_commit(T = comp('.', [H, Tl]),
                        ( static_list(Tl, MT), maybe_cons(MT, H, M) ),
                        M = nothing)).

%  other_args(+Args, +Pos, -Others): Args without the one at Pos (0-based).
other_args(As, Pos, Others) :-
    numbered_list(As, 0, NAs),
    findall(A, ( member(J-A, NAs), J =\= Pos ), Others).

init_of([X|Xs], I) :-
    init_of_(Xs, X, I).

init_of_([], _, []).
init_of_([Y|Ys], X, [X|I]) :-
    init_of_(Ys, Y, I).

last_of([X|Xs], L) :-
    last_of_(Xs, X, L).

last_of_([], X, X).
last_of_([Y|Ys], _, L) :-
    last_of_(Ys, Y, L).
