/*  formula.pl - closed forms for one output position, using mnns's
    AlgebraPLOp.

    For a position k and an integer input N over a domain Lo..Hi, plop2
    samples the character codes of position k and asks
    mnn_algebraplop:infer_sequence_formula/2 (github.com/luciangreen/mnns,
    prolog/algebraplop/algebraplop.pl) for a formula.  When SWI-Prolog or
    mnns is not available, the same inference is run by a direct
    transcription of that predicate (same shapes, same order, same held-out
    check).  Either way the formula is then re-checked on every sample
    before it is used, and the generated code guards it with the sampled
    domain.

    Formulas: constant(V), linear(S, I), quadratic(I, D1, D2),
    exponential(I, B), polynomial(Cs).
*/

formula_term(constant(V), comp(constant, [int(V)])).
formula_term(linear(S, I), comp(linear, [int(S), int(I)])).
formula_term(quadratic(I, D1, D2), comp(quadratic, [int(I), int(D1), int(D2)])).
formula_term(exponential(I, B), comp(exponential, [int(I), int(B)])).
formula_term(polynomial(Cs), comp(polynomial, [L])) :-
    maplist(int_t, Cs, Ts),
    list_t(Ts, L).

show_formula(F, S) :-
    formula_term(F, T),
    show_term_q(T, S).

eval_formula(constant(V), _, V).
eval_formula(linear(S, I), P, X) :-
    X is S * P + I.
eval_formula(quadratic(I, D1, D2), P, X) :-
    X is I + D1 * P + D2 * (P * (P - 1) div 2).
eval_formula(exponential(I, B), P, X) :-
    X is I * B ^ P.
eval_formula(polynomial(Cs), P, X) :-
    numbered_list(Cs, 0, NCs),
    foldl(poly_term(P), NCs, 0, X).

poly_term(P, J-C, A0, A) :-
    binom(P, J, B),
    A is A0 + C * B.

binom(N, J, B) :-
    if_commit(J > N,
              B = 0,
              ( Lo is N - J + 1,
                range_product(Lo, N, Num),
                range_product(1, J, Den),
                B is Num div Den )).

range_product(Lo, Hi, P) :-
    if_commit(Lo > Hi, P = 1, ( Lo1 is Lo + 1, range_product(Lo1, Hi, P1), P is Lo * P1 )).

%  formula_expr(+Formula, +P, -Expr): an arithmetic expression for is/2 in
%  the position variable P.
formula_expr(constant(V), _, int(V)).
formula_expr(linear(S, I), P, comp('+', [comp('*', [int(S), P]), int(I)])).
formula_expr(quadratic(I, D1, D2), P,
             comp('+', [comp('+', [int(I), comp('*', [int(D1), P])]),
                        comp('*', [int(D2), comp('//', [comp('*', [P, comp('-', [P, int(1)])]), int(2)])])])).
formula_expr(exponential(I, B), P, comp('*', [int(I), comp('^', [int(B), P])])).
formula_expr(polynomial(Cs), P, E) :-
    numbered_list(Cs, 0, NCs),
    maplist(poly_expr(P), NCs, Terms),
    Terms = [T0|Ts],
    foldl(plus_expr, Ts, T0, E).

plus_expr(B, A, comp('+', [A, B])).

poly_expr(P, J-C, comp('*', [int(C), B])) :-
    binom_expr(J, P, B).

%  C(P, j) = P (P-1) ... (P-j+1) // j!
binom_expr(J, P, E) :-
    if_commit(J =:= 0,
              E = int(1),
              ( J1 is J - 1,
                findall(comp('-', [P, int(I)]), between(0, J1, I), [F0|Fs]),
                foldl(times_expr, Fs, F0, Prod),
                range_product(1, J, Fact),
                E = comp('//', [Prod, int(Fact)]) )).

times_expr(B, A, comp('*', [A, B])).

%  infer_native(+Codes, -MaybeFormula): direct transcription of
%  mnn_algebraplop:infer_sequence_formula/2.
infer_native(Xs, M) :-
    length(Xs, L),
    if_commit(L < 3,
              M = nothing,
              ( Xs = [X0|_],
                if_commit(all_equal(Xs, X0),
                          M = just(constant(X0)),
                          first_formula(Xs, M)) )).

all_equal([], _).
all_equal([X|Xs], Y) :-
    X =:= Y,
    all_equal(Xs, Y).

first_formula(Xs, M) :-
    if_commit(( try_shape(Xs, F), fits(F, Xs) ), M = just(F), M = nothing).

%  try_shape/2 is a relation, tried in order: linear, quadratic,
%  geometric, then polynomials of degree 3 .. length - 2.
try_shape([I, S2|_], linear(S, I)) :-
    S is S2 - I.
try_shape([I, S2, S3, _|_], quadratic(I, D1, D2)) :-
    D1 is S2 - I,
    D2 is (S3 - S2) - D1.
try_shape([I, S2|_], exponential(I, B)) :-
    I =\= 0,
    S2 mod I =:= 0,
    B is S2 div I.
try_shape(Xs, polynomial(Cs)) :-
    length(Xs, L),
    Max is L - 2,
    between(3, Max, D),
    D1 is D + 1,
    take(D1, Xs, Prefix),
    forward_diffs(Prefix, Cs),
    last_of(Cs, Last),
    Last =\= 0.

:- relation(try_shape/2).

forward_diffs([], []).
forward_diffs([V|Vs], [V|Cs]) :-
    if_commit(Vs == [],
              Cs = [],
              ( diffs([V|Vs], Ds), forward_diffs(Ds, Cs) )).

diffs([X|Xs], Ds) :-
    diffs_(Xs, X, Ds).

diffs_([], _, []).
diffs_([B|Bs], A, [D|Ds]) :-
    D is B - A,
    diffs_(Bs, B, Ds).

fits(F, Xs) :-
    numbered_list(Xs, 0, NXs),
    if_commit(( member(P-X, NXs), eval_formula(F, P, Y), Y =\= X ), fail, true).

%  infer_with_mnns(+Dir, +Codes, -Either): right(MaybeFormula) or
%  left(WhyMnnsWasNotUsed).
infer_with_mnns(Dir, Xs, E) :-
    format(atom(File), "~w/prolog/algebraplop/algebraplop.pl", [Dir]),
    atomic_list_concat(Xs, ',', XA),
    format(atom(Goal), "use_module('~w'), mnn_algebraplop:infer_sequence_formula([~w], F), writeq(F), nl", [File, XA]),
    catch(( process_create(path(swipl), ['-q', '-g', Goal, '-t', halt],
                           [stdout(pipe(O)), stderr(pipe(Er)), process(Pid)]),
            read_string(O, _, OS), read_string(Er, _, ES), close(O), close(Er),
            process_wait(Pid, Status),
            mnns_answer(Status, OS, ES, E) ),
          X,
          ( format(string(M), "swipl not available: ~w", [X]), E = left(M) )).

mnns_answer(Status, OS, ES, E) :-
    if_commit(Status == exit(0),
              ( parse_term_string(OS, PE),
                if_commit(PE = right(T-_-_),
                          ( from_mnns(T, MF), E = right(MF) ),
                          ( PE = left(Why), format(string(M), "could not read mnns's answer ~q: ~s", [OS, Why]), E = left(M) )) ),
              ( string_concat(OS, ES, All), string_concat("mnns failed: ", All, M), E = left(M) )).

from_mnns(T, M) :-
    if_commit(T = comp(formula, [Shape, _]), from_shape(Shape, M), M = nothing).

from_shape(S, M) :-
    if_commit(S = comp(constant, [int(V)]), M = just(constant(V)),
    if_commit(S = comp(linear, [int(A), int(B)]), M = just(linear(A, B)),
    if_commit(S = comp(quadratic, [int(I), int(A), int(B)]), M = just(quadratic(I, A, B)),
    if_commit(S = comp(exponential, [int(I), int(B)]), M = just(exponential(I, B)),
    if_commit(( S = comp(polynomial, [L]), static_list(L, just(Ts)), ints_of(Ts, Cs) ), M = just(polynomial(Cs)),
              M = nothing))))).

ints_of([], []).
ints_of([int(I)|Ts], [I|Is]) :-
    ints_of(Ts, Is).
