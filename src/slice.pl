/*  slice.pl - per-character demand slicing with proofs.

    For an algorithm p(In..., Out) and a position k, plop2 writes a
    separate program that computes only element k of Out:

      p__chark(In..., C)        C is element k of Out (fails if there is none)
      p__chark__r(In..., R)     R = c(C), or R = none if Out has no element k
      p__chark__alt(In..., R)   one clause per source clause (first answer wins)

    Each clause of p__chark__alt keeps a subsequence of the source clause's
    goals and ends with an element expression for element k of the output:
    a goal is kept if it binds a variable the element needs, or if it may
    fail; a goal that only builds other data is dropped only with a totality
    certificate; the goal that produces the output (or a part of it) is
    consumed by the element expression.  Every clause is recorded as a
    proof step with its derivation (see plop_proof.pl and
    docs/proof_rules.md).

    Data:
      spec(F/N, J, K)                a specialised program (J 0-based output)
      sres(Clauses, Used, Disp, Steps, Notes)
      gs(Next, Requests, Disp, NotesRev)       the generator state
      senv(Prog, Used, Base, Full)             Full: ordset of variable ids
      sctx(Visible, Bound, Ground)             Bound, Ground: ordsets
      ex(Node, Needs, Consumed, Conflicts)     an element expression
      slc(Kept, Dropped, Consumed, Needs, Conflicts)
*/

spec_name(spec(F/N, J, K), Name) :-
    N1 is N - 1,
    if_commit(J =:= N1,
              format(atom(Name), "~w__char~d", [F, K]),
              ( J1 is J + 1, format(atom(Name), "~w__a~d_char~d", [F, J1, K]) )).

alt_name(Sp, Name) :-
    spec_name(Sp, S),
    atom_concat(S, '__alt', Name).

r_name(Sp, Name) :-
    spec_name(Sp, S),
    atom_concat(S, '__r', Name).

%  The dispatcher for positions 1..K of one output argument.
disp_name(F/_, J, K, Name) :-
    J1 is J + 1,
    format(atom(Name), "~w__a~d_upto~d_r", [F, J1, K]).

spec_term(spec(F/N, J, K), comp(spec, [comp('/', [atom(F), int(N)]), int(J), int(K)])).

% ---------------------------------------------------------------------------
% Generation state

fresh_s(Name, var(I, Name), gs(I, R, D, N), gs(I1, R, D, N)) :-
    I1 is I + 1.

request_s(Sp, gs(I, R, D, N), gs(I, R1, D, N)) :-
    ord_add_element(R, Sp, R1).

request_disp_s(T, gs(I, R, D, N), gs(I, R, D1, N)) :-
    ord_add_element(D, T, D1).

note_s(Note, gs(I, R, D, N), gs(I, R, D, [Note|N])).

%  e(Rule, Subject, K, R, Goal, Subs, Info)
enode(Rule, Subj, K, R, Goal, Subs, Info, comp(e, [atom(Rule), Subj, int(K), R, Goal, SL, Info])) :-
    list_t(Subs, SL).

goal_of(T, G) :-
    if_commit(T = comp(e, [_, _, _, _, G0, _, _]), G = G0,
              if_commit(T = comp(cl, [_, _, C, _]), G = C, G = T)).

ex_node(ex(N, _, _, _), N).
ex_needs(ex(_, N, _, _), N).
ex_consumed(ex(_, _, C, _), C).
ex_conflicts(ex(_, _, _, C), C).

% ---------------------------------------------------------------------------
% Entry point

%  slice_positions(+Prog, +Key, +OutArg, +N, -SliceResult)
slice_positions(Prog, Key, OutArg, N, R) :-
    findall(spec(Key, OutArg, K), between(1, N, K), Roots0),
    sort(Roots0, Roots),
    map_empty(E),
    slice_loop(E, 0, Prog, Roots, R).

slice_loop(Used, Iter, Prog, Roots, R) :-
    generate_all(Used, Prog, Roots, R0),
    R0 = sres(_, Used1, _, _, _),
    if_commit(same_used(Used1, Used),
              R = R0,
              if_commit(Iter > 50,
                        R = R0,
                        ( Iter1 is Iter + 1, slice_loop(Used1, Iter1, Prog, Roots, R) ))).

same_used(A, B) :-
    map_pairs(A, PA),
    map_pairs(B, PB),
    PA == PB.

generate_all(Used, Prog, Roots, R) :-
    map_empty(E),
    gen_go(Roots, [], E, E, [], [], [], Used, Prog, R).

gen_go(Pending, Done, Acc, UsedAcc, Disp, Steps, Notes, Used, Prog, R) :-
    if_commit(Pending == [],
              R = sres(Acc, UsedAcc, Disp, Steps, Notes),
              ( Pending = [Sp|Rest],
                slice_spec(Prog, Used, Sp, Cls, UsedSp, Reqs, Ds, St, Ns),
                ord_add_element(Done, Sp, Done1),
                ord_subtract(Reqs, Done1, R1),
                ord_subtract(R1, Rest, NewReqs),
                ord_union(Rest, NewReqs, Pending1),
                map_put(Sp, Cls, Acc, Acc1),
                map_put(Sp, UsedSp, UsedAcc, UsedAcc1),
                ord_union(Disp, Ds, Disp1),
                conc(Steps, St, Steps1),
                conc(Notes, Ns, Notes1),
                gen_go(Pending1, Done1, Acc1, UsedAcc1, Disp1, Steps1, Notes1, Used, Prog, R) )).

slice_spec(Prog, Used, Sp, Cls, UsedU, ReqsU, DispU, Steps, Notes) :-
    Sp = spec(Key, _, _),
    prog_preds(Prog, Preds),
    map_find(Preds, Key, [], Clauses),
    numbered_list(Clauses, 1, NCls),
    maplist(slice_clause(Prog, Used, Sp), NCls, Results),
    findall(C, member(r(C, _, _, _, _, _), Results), Cls),
    findall(U, member(r(_, U, _, _, _, _), Results), Us),
    ord_union(Us, UsedU),
    findall(Q, member(r(_, _, Q, _, _, _), Results), Qs),
    ord_union(Qs, ReqsU),
    findall(D, member(r(_, _, _, D, _, _), Results), Dss),
    ord_union(Dss, DispU),
    findall(S, member(r(_, _, _, _, S, _), Results), Steps),
    findall(Nl, member(r(_, _, _, _, _, Nl), Results), Nls),
    concat_lists(Nls, Notes).

slice_clause(Prog, Used, Sp, I-clause(H, Body, NV), Result) :-
    Sp = spec(_, J, _),
    goal_args(H, Args),
    other_args(Args, J, Inputs),
    maplist(term_var_ids, Inputs, IVs),
    ord_union(IVs, Bound0),
    conj_list(Body, Gs),
    slice_attempt([], 0, Prog, Used, Sp, I, H, Body, NV, Args, Bound0, Gs, Result).

slice_attempt(Full, Iter, Prog, Used, Sp, I, H, Body, NV, Args, Bound0, Gs, Result) :-
    Sp = spec(_, J, K),
    Env = senv(Prog, Used, NV, Full),
    NV1 is NV + 1,
    S0 = gs(NV1, [], [], []),
    fresh_s('R', R, S0, S1),
    J1 is J + 1,
    nth_det(J1, Args, just(OutT)),
    term_expr(Env, sctx(Gs, Bound0, Bound0), OutT, K, R, Ex, S1, St),
    ex_needs(Ex, Needs),
    ex_consumed(Ex, Consumed),
    close_over(Env, Bound0, Bound0, Gs, Needs, Consumed, Sl),
    ex_conflicts(Ex, C1),
    Sl = slc(_, _, _, _, C2),
    ord_union(C1, C2, Conflicts),
    if_commit(( Conflicts \== [], Iter < 20 ),
              ( ord_union(Full, Conflicts, Full1), Iter1 is Iter + 1,
                slice_attempt(Full1, Iter1, Prog, Used, Sp, I, H, Body, NV, Args, Bound0, Gs, Result) ),
              slice_finish(Sp, I, H, Body, Args, Gs, R, Ex, Sl, St, Result)).

slice_finish(Sp, I, H, Body, Args, Gs, R, Ex, Sl, St, r(Clause, UsedP, Reqs, Disp, Step, Notes)) :-
    Sp = spec(_, J, _),
    Sl = slc(Kept, _, _, _, _),
    pick_kept(Kept, Gs, KeptGs),
    ex_node(Ex, Node),
    goal_of(Node, EG),
    conc(KeptGs, [EG], BGs),
    mk_conj(BGs, NewBody),
    replace_nth0(Args, J, R, NewArgs),
    alt_name(Sp, AN),
    NewHead = comp(AN, NewArgs),
    St = gs(Next, Reqs, Disp, NotesR),
    Clause = clause(NewHead, NewBody, Next),
    rev(NotesR, Notes),
    spec_term(Sp, ST),
    slice_term(Sl, SlT),
    Step = comp(slice_step, [ST, int(I), comp(':-', [H, Body]), comp(':-', [NewHead, NewBody]), SlT, Node]),
    used_params(J, Clause, UsedP).

pick_kept(Kept, Gs, Out) :-
    numbered_list(Gs, 1, NGs),
    findall(G, ( member(Ix-G, NGs), memberchk(Ix, Kept) ), Out).

replace_nth0(Args, J, X, Out) :-
    numbered_list(Args, 0, NAs),
    maplist(replace_at(J, X), NAs, Out).

replace_at(J, X, I-A, B) :-
    if_commit(I =:= J, B = X, B = A).

%  used_params(+J, +Clause, -Set): the input positions a program clause
%  reads: a non-variable head argument, or a variable that occurs elsewhere.
used_params(J, clause(H, B, _), Set) :-
    goal_args(H, Args),
    conc(Args, [B], All),
    findall(V, ( member(T, All), all_var_occ(T, Occ), member(V, Occ) ), Vs),
    msort(Vs, SVs),
    numbered_list(Args, 0, NAs),
    findall(Ix, ( member(Ix-A, NAs), Ix =\= J, used_arg(A, SVs) ), Ixs),
    sort(Ixs, Set).

%  semidet
used_arg(A, SVs) :-
    if_commit(A = var(_, _),
              ( term_var_ids(A, Ids), member(V, Ids), occurs_twice(V, SVs) ),
              true).

:- relation(used_arg/2).

occurs_twice(V, SVs) :-
    append(_, [V, V|_], SVs).

:- relation(occurs_twice/2).

all_var_occ(T, Occ) :-
    if_commit(T = var(V, _), Occ = [V],
              if_commit(T = comp(_, As), ( maplist(all_var_occ, As, Os), concat_lists(Os, Occ) ), Occ = [])).

% ---------------------------------------------------------------------------
% Groundness and first occurrences (inputs are ground)

ground_functional(['atom_codes/2', 'atom_chars/2', 'number_codes/2', 'number_chars/2',
                   'atom_length/2', 'char_code/2', 'upcase_atom/2', 'downcase_atom/2',
                   'atomic_list_concat/2', 'atomic_list_concat/3', 'atom_concat/3',
                   'string_concat/3', 'string_chars/2', 'atom_string/2',
                   'append/3', 'reverse/2', 'length/2', 'nth0/3', 'nth1/3',
                   'last/2', 'sum_list/2', 'max_list/2', 'min_list/2', 'msort/2', 'sort/2',
                   'succ/2', 'plus/3']).

ground_reversible(['atom_codes/2', 'atom_chars/2', 'char_code/2', 'string_chars/2']).

%  ground_after(+Ground, +Goal, -Ground): variables ground after a goal.
ground_after(Gr, G, Gr1) :-
    if_commit(( G = comp('=', [A, B]), gnd_in(A, Gr) ),
              ( term_var_ids(B, BV), ord_union(Gr, BV, Gr1) ),
    if_commit(( G = comp('=', [A, B]), gnd_in(B, Gr) ),
              ( term_var_ids(A, AV), ord_union(Gr, AV, Gr1) ),
    if_commit(( G = comp(is, [X, E]), gnd_in(E, Gr) ),
              ( term_var_ids(X, XV), ord_union(Gr, XV, Gr1) ),
    if_commit(( G = comp(F, As), As = [_|_], length(As, N), key_atom(F, N, KA),
                ground_functional(Fun), memberchk(KA, Fun),
                init_of(As, Init), all_gnd(Init, Gr) ),
              ( last_of(As, L), term_var_ids(L, LV), ord_union(Gr, LV, Gr1) ),
    if_commit(( G = comp(F, As), As = [_|_], length(As, N), key_atom(F, N, KA),
                ground_reversible(Rev), memberchk(KA, Rev),
                last_of(As, L), gnd_in(L, Gr) ),
              ( init_of(As, Init), maplist(term_var_ids, Init, IVs), ord_union([Gr|IVs], Gr1) ),
              Gr1 = Gr))))).

gnd_in(T, Gr) :-
    term_var_ids(T, V),
    ord_subset(V, Gr).

all_gnd([], _).
all_gnd([T|Ts], Gr) :-
    gnd_in(T, Gr),
    all_gnd(Ts, Gr).

%  with_produced(+Bound, +Goals, -Pairs): Goal-NewVars for each goal.
with_produced(Bound, Gs, Ps) :-
    with_produced_(Gs, Bound, Ps).

with_produced_([], _, []).
with_produced_([G|Gs], Seen, [G-Prod|Ps]) :-
    term_var_ids(G, Vs),
    ord_subtract(Vs, Seen, Prod),
    ord_union(Seen, Vs, Seen1),
    with_produced_(Gs, Seen1, Ps).

produced_in(Bound, Gs, Set) :-
    with_produced(Bound, Gs, Ps),
    pairs_values(Ps, Vs),
    ord_union(Vs, Set).

ground_through(Gr, Gs, Gr1) :-
    foldl(ground_after_f, Gs, Gr, Gr1).

ground_after_f(G, Gr, Gr1) :-
    ground_after(Gr, G, Gr1).

%  find_producer(+Bound, +Goals, +V, -Maybe): just(G-Before-After), the goal
%  that binds V first.
find_producer(Bound, Gs, V, M) :-
    with_produced(Bound, Gs, Ps),
    numbered_list(Ps, 0, NPs),
    if_commit(( member(Ix-(G-Prod), NPs), ord_memberchk(V, Prod) ),
              ( take(Ix, Gs, Before), Ix1 is Ix + 1, drop(Ix1, Gs, After), M = just(G-Before-After) ),
              M = nothing).

% ---------------------------------------------------------------------------
% Element expressions

nth_r(K, T, R, comp(plop2_nth_r, [int(K), T, R])).

c_of(X, comp(c, [X])).

ite_t(C, T, E, comp(';', [comp('->', [C, T]), E])).

none_g(R, comp('=', [R, atom(none)])).

local_vars(senv(_, _, Base, _), T, Vs) :-
    term_var_ids(T, All),
    findall(V, ( member(V, All), V < Base ), Vs).

leaf(Rule, Subj, K, R, Goal, Info, Needs, ex(Node, Needs, [], [])) :-
    enode(Rule, Subj, K, R, Goal, [], Info, Node).

%  term_expr(+Env, +Ctx, +T, +K, +R, -Ex, +S0, -S): element K of a term.
term_expr(Env, Cx, T, K, R, Ex, S0, S) :-
    term_shape_s(T, K, Shape),
    term_expr_(Shape, Env, Cx, T, K, R, Ex, S0, S).

term_shape_s(T, K, Shape) :-
    if_commit(T = var(_, _), Shape = var,
    if_commit(T = comp('.', [_, _]), if_commit(K =:= 1, Shape = head, Shape = tail),
    if_commit(T == atom('[]'), Shape = none,
    if_commit(T = atom(_), Shape = atom,
    if_commit(T = int(_), Shape = int,
              Shape = nth))))).

term_expr_(var, Env, Cx, T, K, R, Ex, S0, S) :-
    T = var(V, _),
    char_expr(Env, Cx, V, T, K, R, Ex, S0, S).
term_expr_(head, Env, _, T, K, R, Ex, S, S) :-
    T = comp('.', [H, _]),
    c_of(H, CH),
    local_vars(Env, H, LV),
    leaf(el_head, T, K, R, comp('=', [R, CH]), atom(none), LV, Ex).
term_expr_(tail, Env, Cx, T, K, R, ex(Node, N, C, Cf), S0, S) :-
    T = comp('.', [_, Tl]),
    K1 is K - 1,
    term_expr(Env, Cx, Tl, K1, R, ex(SubNode, N, C, Cf), S0, S),
    goal_of(SubNode, G),
    enode(el_tail, T, K, R, G, [SubNode], atom(none), Node).
term_expr_(none, _, _, T, K, R, Ex, S, S) :-
    none_g(R, G),
    leaf(el_none, T, K, R, G, atom(none), [], Ex).
term_expr_(atom, _, _, T, K, R, Ex, S, S) :-
    T = atom(A),
    atom_codes(A, Cs),
    text_const(Cs, T, K, R, Ex).
term_expr_(int, _, _, T, K, R, Ex, S, S) :-
    T = int(X),
    number_codes(X, Cs),
    text_const(Cs, T, K, R, Ex).
term_expr_(nth, Env, _, T, K, R, Ex, S, S) :-
    nth_r(K, T, R, G),
    local_vars(Env, T, LV),
    leaf(el_nth, T, K, R, G, atom(none), LV, Ex).

text_const(Cs, T, K, R, Ex) :-
    length(Cs, L),
    if_commit(K =< L,
              ( nth_det(K, Cs, just(C)), char_code(A, C), c_of(atom(A), CA),
                leaf(el_const, T, K, R, comp('=', [R, CA]), atom(none), [], Ex) ),
              ( none_g(R, G), leaf(el_none, T, K, R, G, atom(none), [], Ex) )).

%  Element K of a variable: from its full value, or from its producer.
char_expr(Env, Cx, V, VT, K, R, Ex, S0, S) :-
    Env = senv(_, _, _, Full),
    if_commit(ord_memberchk(V, Full),
              ( S = S0, nth_r(K, VT, R, G), leaf(el_nth, VT, K, R, G, atom(none), [V], Ex) ),
              ( Cx = sctx(Visible, Bound, _),
                find_producer(Bound, Visible, V, MP),
                char_expr_p(MP, Env, Cx, V, VT, K, R, Ex, S0, S) )).

char_expr_p(nothing, _, sctx(_, Bound, _), V, VT, K, R, Ex, S, S) :-
    if_commit(ord_memberchk(V, Bound),
              ( nth_r(K, VT, R, G), leaf(el_nth, VT, K, R, G, atom(none), [V], Ex) ),
              ( none_g(R, G), leaf(el_none, VT, K, R, G, atom(none), [], Ex) )).
char_expr_p(just(G-Before-After), Env, Cx, V, VT, K, R, Ex, S0, S) :-
    alias_of(G, Before, Cx, V, MA),
    char_alias(MA, G, Before, After, Env, Cx, V, VT, K, R, Ex, S0, S).

char_alias(just(W-WT), G, Before, After, Env, sctx(_, B, Gr), _, VT, K, R,
           ex(Node, N, [G|C], Cf), S0, S) :-
    conc(Before, After, Vis),
    char_expr(Env, sctx(Vis, B, Gr), W, WT, K, R, ex(SubNode, N, C, Cf), S0, S),
    goal_of(SubNode, SG),
    enode(el_alias, VT, K, R, SG, [SubNode], G, Node).
char_alias(nothing, G, Before, _, Env, Cx, V, VT, K, R, ex(Node, N, [G|C], Cf), S0, S) :-
    producer_expr(Env, Cx, Before, G, V, VT, K, R, ex(Node, N, C, Cf), S0, S).

alias_of(G, Before, sctx(_, Bound, _), V, M) :-
    maplist(term_var_ids, Before, BVs),
    ord_union([Bound|BVs], Seen),
    if_commit(( G = comp('=', [var(X, _), B]), B = var(Y, _), X =:= V, Y =\= V, ord_nonmember(Y, Seen) ),
              M = just(Y-B),
              if_commit(( G = comp('=', [A, var(Y2, _)]), A = var(X2, _), Y2 =:= V, X2 =\= V,
                          ord_nonmember(X2, Seen) ),
                        M = just(X2-A),
                        M = nothing)).

is_v(V, X) :-
    X = var(I, _),
    I =:= V.

producer_expr(Env, Cx, Before, G, V, VT, K, R, Ex, S0, S) :-
    producer_kind(G, V, Env, Kind),
    producer_(Kind, Env, Cx, Before, G, V, VT, K, R, Ex, S0, S).

producer_kind(G, V, Env, Kind) :-
    if_commit(( G = comp('=', [X, T]), is_v(V, X) ), Kind = via(el_unify, T),
    if_commit(( G = comp('=', [T, X]), is_v(V, X) ), Kind = via(el_unify, T),
    if_commit(G = comp(';', [comp('->', [C, T]), E]), Kind = branches(just(C), T, E),
    if_commit(G = comp('->', [C, T]), Kind = branches(just(C), T, atom(fail)),
    if_commit(G = comp(if_commit, [C, T, E]), Kind = branches(just(C), T, E),
    if_commit(G = comp(';', [A, B]), Kind = branches(nothing, A, B),
    if_commit(( G = comp(append, [A, B, X]), is_v(V, X) ), Kind = chain(list, [A, B]),
    if_commit(( G = comp(F, [A, B, X]), memberchk(F, [atom_concat, string_concat]), is_v(V, X) ),
              Kind = chain(text, [A, B]),
    if_commit(( G = comp(atomic_list_concat, [L, X]), is_v(V, X), static_list(L, just(Ps)) ),
              Kind = chain(text, Ps),
    if_commit(( G = comp(atomic_list_concat, [L, Sep, X]), is_v(V, X), static_list(L, just(Ps)) ),
              ( interleave_t(Sep, Ps, IPs), Kind = chain(text, IPs) ),
    if_commit(( G = comp(F, [A, X]), memberchk(F, [atom_chars, string_chars, atom_string]), is_v(V, X) ),
              Kind = via(el_same_text, A),
    if_commit(( G = comp(F, [X, L]), memberchk(F, [atom_chars, string_chars]), is_v(V, X) ),
              Kind = via(el_same_text, L),
    if_commit(( G = comp(atom_codes, [A, X]), is_v(V, X) ), Kind = convert(el_codes_of_text, A, true),
    if_commit(( G = comp(atom_codes, [X, L]), is_v(V, X) ), Kind = convert(el_text_of_codes, L, false),
    if_commit(( G = comp(number_codes, [Num, X]), is_v(V, X) ), Kind = number_codes(Num),
    if_commit(( G = comp(number_chars, [Num, X]), is_v(V, X) ), Kind = number_chars(Num),
    if_commit(( G = comp(atom_number, [X, Num]), is_v(V, X) ), Kind = number_chars(Num),
    if_commit(( G = comp(reverse, [L, X]), is_v(V, X) ), Kind = reverse(L),
    if_commit(( G = comp(maplist, [F, L, X]), is_v(V, X), is_var_t(F, false), is_callable_t(F, true),
                add_args(F, [var(-1, 'X'), var(-2, 'Y')], just(_)) ),
              Kind = maplist(F, L),
    if_commit(user_output(G, V, Env, just(Key-Pos)), Kind = user(Key, Pos),
              Kind = fallback)))))))))))))))))))).

producer_(via(Rule, T), Env, Cx, Before, G, _, VT, K, R, ex(Node, N, C, Cf), S0, S) :-
    any_expr(Env, Cx, Before, T, K, R, ex(SubNode, N, C, Cf), S0, S),
    goal_of(SubNode, SG),
    enode(Rule, VT, K, R, SG, [SubNode], G, Node).
producer_(branches(MC, T, E), Env, Cx, Before, G, V, VT, K, R, Ex, S0, S) :-
    branches(MC, T, E, Env, Cx, Before, G, V, VT, K, R, Ex, S0, S).
producer_(chain(Mode, Parts), Env, Cx, Before, G, _, VT, K, R, Ex, S0, S) :-
    chain_of(Mode, Parts, Env, Cx, Before, G, VT, K, R, Ex, S0, S).
producer_(convert(Rule, T, FromText), Env, Cx, Before, G, _, VT, K, R, ex(Node, N, C, Cf), S0, S) :-
    fresh_s('R0', R0, S0, S1),
    fresh_s('Ch', Ch, S1, S2),
    fresh_s('Code', Code, S2, S3),
    any_expr(Env, Cx, Before, T, K, R0, ex(SubNode, N, C, Cf), S3, S),
    if_commit(FromText == true,
              ( c_of(Ch, Tc), Test = comp('=', [R0, Tc]), c_of(Code, Res) ),
              ( c_of(Code, Tc), Test = comp('=', [R0, Tc]), c_of(Ch, Res) )),
    goal_of(SubNode, SG),
    none_g(R, NG),
    mk_conj([comp(char_code, [Ch, Code]), comp('=', [R, Res])], Then),
    ite_t(Test, Then, NG, Ite),
    mk_conj([SG, Ite], Goal),
    enode(Rule, VT, K, R, Goal, [SubNode], G, Node).
producer_(number_codes(Num), Env, _, _, G, _, VT, K, R, ex(Node, LV, [], []), S0, S) :-
    fresh_s('R0', R0, S0, S1),
    fresh_s('Ch', Ch, S1, S2),
    fresh_s('Code', Code, S2, S),
    nth_r(K, Num, R0, NG0),
    c_of(Ch, CCh),
    c_of(Code, CCode),
    none_g(R, NG),
    mk_conj([comp(char_code, [Ch, Code]), comp('=', [R, CCode])], Then),
    ite_t(comp('=', [R0, CCh]), Then, NG, Ite),
    mk_conj([NG0, Ite], Goal),
    enode(el_number_codes, VT, K, R, Goal, [], G, Node),
    local_vars(Env, Num, LV).
producer_(number_chars(Num), Env, _, _, G, _, VT, K, R, ex(Node, LV, [], []), S, S) :-
    nth_r(K, Num, R, NG),
    enode(el_number_chars, VT, K, R, NG, [], G, Node),
    local_vars(Env, Num, LV).
producer_(reverse(L), Env, _, _, G, _, VT, K, R, ex(Node, LV, [], []), S0, S) :-
    fresh_s('Len', Len, S0, S1),
    fresh_s('I', Ix, S1, S2),
    fresh_s('X', Xv, S2, S3),
    format(string(Note), "element ~d of reverse/2 needs the whole input list", [K]),
    note_s(Note, S3, S),
    c_of(Xv, CX),
    none_g(R, NG),
    mk_conj([comp(nth1, [Ix, L, Xv]), comp('=', [R, CX])], Then),
    ite_t(comp('>=', [Ix, int(1)]), Then, NG, Ite),
    mk_conj([comp(length, [L, Len]),
             comp(is, [Ix, comp('+', [comp('-', [Len, int(K)]), int(1)])]),
             Ite], Goal),
    enode(el_reverse, VT, K, R, Goal, [], G, Node),
    local_vars(Env, L, LV).
producer_(maplist(F, L), Env, Cx, Before, G, _, VT, K, R, ex(Node, Needs, C, Cf), S0, S) :-
    fresh_s('R0', R0, S0, S1),
    fresh_s('X', Xv, S1, S2),
    fresh_s('Y', Yv, S2, S3),
    any_expr(Env, Cx, Before, L, K, R0, ex(SubNode, N0, C, Cf), S3, S),
    add_args(F, [Xv, Yv], just(Call)),
    goal_of(SubNode, SG),
    c_of(Xv, CX),
    c_of(Yv, CY),
    none_g(R, NG),
    mk_conj([Call, comp('=', [R, CY])], Then),
    ite_t(comp('=', [R0, CX]), Then, NG, Ite),
    mk_conj([SG, Ite], Goal),
    enode(el_maplist, VT, K, R, Goal, [SubNode], G, Node),
    local_vars(Env, F, FV),
    ord_union(N0, FV, Needs).
producer_(user(Key, Pos), Env, Cx, Before, G, V, VT, K, R, Ex, S0, S) :-
    if_commit(ground_args(Env, Cx, Before, G, Key, Pos, [K]),
              user_spec(Key, Pos, Env, G, VT, K, R, Ex, S0, S),
              fallback_expr(G, V, VT, K, R, Ex, S0, S)).
producer_(fallback, _, _, _, G, V, VT, K, R, Ex, S0, S) :-
    fallback_expr(G, V, VT, K, R, Ex, S0, S).

user_spec(Key, Pos, Env, G, VT, K, R, ex(Node, Needs, [], []), S0, S) :-
    Sp = spec(Key, Pos, K),
    Env = senv(_, Used, _, _),
    map_find(Used, Sp, [], UsedSp),
    goal_args(G, As),
    numbered_list(As, 0, NAs),
    foldl(spec_arg(Pos, UsedSp, R), NAs, []-S0, ArgsR-S1),
    rev(ArgsR, Args1),
    request_s(Sp, S1, S),
    numbered_list(Args1, 0, NA1),
    findall(LV, ( member(Ix-A, NA1), Ix =\= Pos, local_vars(Env, A, LV) ), LVs),
    ord_union(LVs, Needs),
    r_name(Sp, RN),
    enode(el_spec, VT, K, R, comp(RN, Args1), [], G, Node).

spec_arg(Pos, UsedSp, R, Ix-A, Acc-S0, [B|Acc]-S) :-
    if_commit(Ix =:= Pos, ( B = R, S = S0 ),
              if_commit(ord_memberchk(Ix, UsedSp), ( B = A, S = S0 ), fresh_s('_', B, S0, S))).

fallback_expr(G, V, VT, K, R, ex(Node, [V], [], [V]), S0, S) :-
    goal_key(G, MK),
    haskell_show_key(MK, KS),
    string_codes(KS, KC),
    take(60, KC, KC60),
    string_codes(K60, KC60),
    format(string(Note), "element ~d: the producer of a variable is kept in full: ~s", [K, K60]),
    note_s(Note, S0, S),
    nth_r(K, VT, R, NG),
    enode(el_nth, VT, K, R, NG, [], atom(none), Node).

%  Haskell's show of Maybe (String, Int)
haskell_show_key(nothing, "Nothing").
haskell_show_key(just(F/N), S) :-
    atom_string(F, FS),
    plop2_show_string(FS, Q),
    format(string(S), "Just (~s,~d)", [Q, N]).

%  plop2_show_string(+Text, -Shown): a string as Haskell's show writes it.
plop2_show_string(T, S) :-
    string_codes(T, Cs),
    show_escape(Cs, Es),
    conc([0'"|Es], `"`, All),
    string_codes(S, All).

show_escape([], []).
show_escape([C|Cs], Out) :-
    show_char(C, Cs, E),
    show_escape(Cs, Rest),
    conc(E, Rest, Out).

show_char(C, Next, E) :-
    if_commit(C =:= 0'", E = `\\"`,
    if_commit(C =:= 0'\\, E = `\\\\`,
    if_commit(C =:= 10, E = `\\n`,
    if_commit(C =:= 9, E = `\\t`,
    if_commit(( C >= 32, C =< 126 ), E = [C],
              ( number_codes(C, D),
                if_commit(( Next = [N|_], N >= 0'0, N =< 0'9 ), conc(D, `\\&`, D1), D1 = D),
                E = [0'\\|D1] )))))).

%  a user predicate whose output argument is exactly V, and V nowhere else
user_output(G, V, senv(Prog, _, _, _), M) :-
    goal_key(G, MK),
    if_commit(( MK = just(Key), prog_lookup(Prog, Key, just(_)),
                goal_args(G, As), numbered_list(As, 0, NAs),
                findall(Ix, ( member(Ix-A, NAs), is_v(V, A) ), [Pos]),
                findall(Vs, ( member(Ix2-A2, NAs), Ix2 =\= Pos, term_var_ids(A2, Vs) ), VLs),
                ord_union(VLs, Others), ord_nonmember(V, Others) ),
              M = just(Key-Pos),
              M = nothing).

%  the arguments a program reads must be ground where the call was
ground_args(senv(_, Used, _, _), sctx(_, _, Ground), Before, G, Key, Pos, Ks) :-
    findall(U, ( member(Kk, Ks), map_find(Used, spec(Key, Pos, Kk), [], U) ), Us),
    ord_union(Us, UsedAll),
    ground_through(Ground, Before, GB),
    goal_args(G, As),
    numbered_list(As, 0, NAs),
    if_commit(( member(Ix-A, NAs), Ix =\= Pos, ord_memberchk(Ix, UsedAll), not_gnd_in(A, GB) ), fail, true).

any_expr(Env, sctx(_, B, Gr), Before, T, K, Out, Ex, S0, S) :-
    if_commit(T = var(Ix, _),
              char_expr(Env, sctx(Before, B, Gr), Ix, T, K, Out, Ex, S0, S),
              term_expr(Env, sctx(Before, B, Gr), T, K, Out, Ex, S0, S)).

%  A producing if-then-else or disjunction: slice each branch.
branches(MC, T, E, Env, Cx, Before, G, V, VT, K, R, ex(Node, Needs, Outer, Conflicts), S0, S) :-
    Cx = sctx(_, Bound, Ground),
    if_commit(MC = just(C), conj_list(C, Cs), Cs = []),
    conj_list(T, Ts),
    conj_list(E, Es),
    produced_in(Bound, Before, PB),
    ord_union(Bound, PB, BoundBefore),
    ground_through(Ground, Before, GroundB),
    concat_lists([Before, Cs, Ts], VisT),
    char_expr(Env, sctx(VisT, Bound, Ground), V, VT, K, R, ExT, S0, S1),
    conc(Before, Es, VisE),
    char_expr(Env, sctx(VisE, Bound, Ground), V, VT, K, R, ExE, S1, S),
    ExT = ex(NodeT, NeedsT, ConsT, CfT),
    ExE = ex(NodeE, NeedsE, ConsE, CfE),
    produced_in(BoundBefore, Cs, PC),
    ord_union(BoundBefore, PC, BoundT),
    ground_through(GroundB, Cs, GroundT),
    close_over(Env, BoundT, GroundT, Ts, NeedsT, ConsT, SlT),
    SlT = slc(_, _, _, NeedsSlT, CfSlT),
    close_over(Env, BoundBefore, GroundB, Cs, NeedsSlT, ConsT, SlC),
    close_over(Env, BoundBefore, GroundB, Es, NeedsE, ConsE, SlE),
    SlC = slc(KeptC, _, _, NeedsC, CfSlC),
    SlE = slc(KeptE, _, _, NeedsSlE, CfSlE),
    SlT = slc(KeptT, _, _, _, _),
    pick_kept(KeptT, Ts, PT),
    pick_kept(KeptE, Es, PE),
    pick_kept(KeptC, Cs, PC1),
    goal_of(NodeT, GT),
    goal_of(NodeE, GE),
    conc(PT, [GT], TGs),
    mk_conj(TGs, ThenG),
    conc(PE, [GE], EGs),
    mk_conj(EGs, ElseG),
    mk_conj(PC1, CondG),
    if_commit(MC == nothing,
              Goal = comp(';', [ThenG, ElseG]),
              if_commit(G = comp(if_commit, _),
                        Goal = comp(if_commit, [CondG, ThenG, ElseG]),
                        ite_t(CondG, ThenG, ElseG, Goal))),
    slice_term(SlC, STC),
    slice_term(SlT, STT),
    slice_term(SlE, STE),
    Info = comp(branch, [G, STC, STT, STE]),
    concat_lists([Cs, Ts, Es], Local),
    conc(ConsT, ConsE, AllCons),
    findall(X, ( member(X, AllCons), not_term_member(X, Local) ), Outer),
    ord_union(NeedsC, NeedsSlE, Needs),
    ord_union([CfT, CfE, CfSlT, CfSlC, CfSlE], Conflicts),
    enode(el_branch, VT, K, R, Goal, [NodeT, NodeE], Info, Node).

ord_nonmember(X, S) :-
    if_commit(ord_memberchk(X, S), fail, true).

not_gnd_in(T, Gr) :-
    if_commit(gnd_in(T, Gr), fail, true).

not_term_member(X, L) :-
    if_commit(term_member(X, L), fail, true).

not_memberchk(X, L) :-
    if_commit(memberchk(X, L), fail, true).

%  semidet: X is an element of L (term equality by variable id)
term_member(X, L) :-
    member(Y, L),
    same_term(X, Y, true).

:- relation(term_member/2).

%  A concatenation: plop2_chain/3 over one closure per part.
chain_of(Mode, Parts, Env, Cx, Before, G, VT, K, R, Ex, S0, S) :-
    foldl(closure_for_acc(Mode, Env, Cx, Before, K), Parts, []-S0, ClsR-S),
    rev(ClsR, Cls),
    findall(C, member(cl3(C, _, _), Cls), Cs),
    list_t(Cs, CL),
    Goal = comp(plop2_chain, [int(K), CL, R]),
    maplist(cl_sub, Cls, Parts, Subs),
    maplist(cl_needs(Env), Cls, Parts, NLs),
    ord_union(NLs, Needs),
    findall(PG, member(cl3(_, cl_chain, comp(chain, [PG, _])), Cls), ChainConsumed),
    findall(Info, member(cl3(_, cl_spec, Info), Cls), SpecConsumed),
    conc(SpecConsumed, ChainConsumed, Consumed),
    closure_prefix(Cs, Prefix, _),
    length(Prefix, LP),
    if_commit(K =< LP,
              ( nth_det(K, Prefix, just(PK)), c_of(PK, CP),
                enode(el_chain_const, VT, K, R, comp('=', [R, CP]), Subs, G, Node),
                Ex = ex(Node, [], ChainConsumed, []) ),
              ( enode(el_chain, VT, K, R, Goal, Subs, G, Node),
                Ex = ex(Node, Needs, Consumed, []) )).

cl_sub(cl3(C, Rule, Info), P, comp(cl, [atom(Rule), P, C, Info])).

cl_needs(Env, cl3(C, Rule, _), P, Needs) :-
    if_commit(Rule == cl_static, Needs = [],
    if_commit(Rule == cl_value, local_vars(Env, P, Needs),
    if_commit(Rule == cl_chain,
              ( chain_items(C, Items),
                findall(LV, ( member(comp(plop2_value, [X]), Items), local_vars(Env, X, LV) ), LVs),
                ord_union(LVs, Needs) ),
              ( goal_args(C, As), maplist(local_vars(Env), As, LVs), ord_union(LVs, Needs) )))).

chain_items(C, Items) :-
    if_commit(( C = comp(plop2_chain_c, [L]), static_list(L, just(Xs)) ), Items = Xs, Items = []).

closure_for_acc(Mode, Env, Cx, Before, K, P, Acc-S0, [Cl|Acc]-S) :-
    closure_for(Mode, Env, Cx, Before, K, P, Cl, S0, S).

%  call(Closure, J, R) gives element J of the part
closure_for(Mode, Env, Cx, Before, K, P, Cl, S0, S) :-
    static_elems(Mode, P, MS),
    if_commit(MS = just(Xs),
              ( list_t(Xs, XL), Cl = cl3(comp(plop2_static, [XL]), cl_static, atom(none)), S = S0 ),
              closure_part(Env, Cx, Before, K, P, Cl, S0, S)).

closure_part(Env, Cx, Before, K, P, Cl, S0, S) :-
    Env = senv(_, Used, _, Full),
    Cx = sctx(_, Bound, _),
    if_commit(( P = var(W, _), ord_nonmember(W, Full),
                find_producer(Bound, Before, W, just(PG-PBefore-_)),
                part_output(Env, PG, W, just(Key-Pos)),
                ok_ground(Env, Cx, Key, Pos, PG, PBefore, K) ),
              ( findall(U, ( between(1, K, Jj), map_find(Used, spec(Key, Pos, Jj), [], U) ), Us),
                ord_union(Us, UsedAny),
                numlist_k(K, Ks1),
                foldl(request_jj(Key, Pos), Ks1, S0, S1),
                request_disp_s(t(Key, Pos, K), S1, S2),
                goal_args(PG, PAs),
                numbered_list(PAs, 0, NPAs),
                foldl(disp_arg(Pos, UsedAny), NPAs, []-S2, ArgsR-S),
                rev(ArgsR, Args1),
                disp_name(Key, Pos, K, DN),
                Cl = cl3(comp(DN, Args1), cl_spec, PG) ),
    if_commit(( P = var(W, _), ord_nonmember(W, Full),
                find_producer(Bound, Before, W, just(PG-PBefore-_)),
                concat_parts(PG, W, just(InnerMode-InnerParts)) ),
              ( maplist(closure_with(InnerMode), InnerParts, Inner),
                findall(C, member(cl3(C, _, _), Inner), ICs),
                list_t(ICs, ICL),
                maplist(cl_sub, Inner, InnerParts, ISubs),
                list_t(ISubs, ISL),
                Cl = cl3(comp(plop2_chain_c, [ICL]), cl_chain, comp(chain, [PG, ISL])),
                S = S0,
                PBefore = PBefore ),
              ( Cl = cl3(comp(plop2_value, [P]), cl_value, atom(none)), S = S0 ))).

numlist_k(K, Ks) :-
    findall(J, between(1, K, J), Ks).

request_jj(Key, Pos, Jj, S0, S) :-
    request_s(spec(Key, Pos, Jj), S0, S).

disp_arg(Pos, UsedAny, Ix-A, Acc-S0, Acc1-S) :-
    if_commit(Ix =:= Pos,
              ( Acc1 = Acc, S = S0 ),
              if_commit(ord_memberchk(Ix, UsedAny),
                        ( Acc1 = [A|Acc], S = S0 ),
                        ( fresh_s('_', B, S0, S), Acc1 = [B|Acc] ))).

closure_with(Mode, P, Cl) :-
    static_elems(Mode, P, MS),
    if_commit(MS = just(Xs),
              ( list_t(Xs, XL), Cl = cl3(comp(plop2_static, [XL]), cl_static, atom(none)) ),
              Cl = cl3(comp(plop2_value, [P]), cl_value, atom(none))).

concat_parts(PG, W, M) :-
    if_commit(( PG = comp(append, [A, B, var(X, _)]), X =:= W ), M = just(list-[A, B]),
    if_commit(( PG = comp(F, [A, B, var(X, _)]), X =:= W, memberchk(F, [atom_concat, string_concat]) ),
              M = just(text-[A, B]),
    if_commit(( PG = comp(atomic_list_concat, [L, var(X, _)]), X =:= W, static_list(L, just(Ps)) ),
              M = just(text-Ps),
    if_commit(( PG = comp(atomic_list_concat, [L, Sep, var(X, _)]), X =:= W, static_list(L, just(Ps)) ),
              ( interleave_t(Sep, Ps, IPs), M = just(text-IPs) ),
              M = nothing)))).

part_output(senv(Prog, _, _, _), PG, W, M) :-
    goal_key(PG, MK),
    if_commit(( MK = just(Key), prog_lookup(Prog, Key, just(_)),
                goal_args(PG, As), numbered_list(As, 0, NAs),
                findall(Ix, ( member(Ix-var(X, _), NAs), X =:= W ), [Pos]),
                findall(Vs, ( member(Ix2-A2, NAs), Ix2 =\= Pos, term_var_ids(A2, Vs) ), VLs),
                ord_union(VLs, Others), ord_nonmember(W, Others) ),
              M = just(Key-Pos),
              M = nothing).

ok_ground(senv(_, Used, _, _), sctx(_, _, Ground), Key, Pos, PG, PBefore, K) :-
    ground_through(Ground, PBefore, GB),
    findall(U, ( between(1, K, Jj), map_find(Used, spec(Key, Pos, Jj), [], U) ), Us),
    ord_union(Us, UsedAny),
    goal_args(PG, As),
    numbered_list(As, 0, NAs),
    if_commit(( member(Ix-A, NAs), Ix =\= Pos, ord_memberchk(Ix, UsedAny), not_gnd_in(A, GB) ), fail, true).

%  closure_prefix(+Closures, -Elements, -Complete): the elements a list of
%  closures certainly starts with, and whether that is all of them.
closure_prefix([], [], true).
closure_prefix([C|Cs], Xs, Complete) :-
    if_commit(( C = comp(plop2_static, [L]), static_list(L, just(Ys)) ),
              ( closure_prefix(Cs, Rest, Complete), conc(Ys, Rest, Xs) ),
              if_commit(( C = comp(plop2_chain_c, [L]), static_list(L, just(Inner)) ),
                        ( closure_prefix(Inner, Ys, Ok),
                          if_commit(Ok == true,
                                    ( closure_prefix(Cs, Rest, Complete), conc(Ys, Rest, Xs) ),
                                    ( Xs = Ys, Complete = false )) ),
                        ( Xs = [], Complete = false ))).

static_elems(list, T, M) :-
    ground_list_t(T, M).
static_elems(text, T, M) :-
    if_commit(T = atom(A),
              ( atom_chars(A, Cs), maplist(char_atom_t, Cs, Ts), M = just(Ts) ),
              if_commit(T = int(X),
                        ( number_codes(X, Codes), atom_codes(XA, Codes), atom_chars(XA, Cs),
                          maplist(char_atom_t, Cs, Ts), M = just(Ts) ),
                        ground_list_t(T, M))).

char_atom_t(C, atom(C)).

ground_list_t(T, M) :-
    if_commit(T == atom('[]'), M = just([]),
              if_commit(( T = comp('.', [H, Tl]), term_var_ids(H, []) ),
                        ( ground_list_t(Tl, M1), maybe_cons(M1, H, M) ),
                        M = nothing)).

interleave_t(S, Xs, Out) :-
    interleave_t_(Xs, S, Out).

interleave_t_([], _, []).
interleave_t_([X|Xs], S, Out) :-
    if_commit(Xs == [], Out = [X], ( interleave_t_(Xs, S, Rest), Out = [X, S|Rest] )).

% ---------------------------------------------------------------------------
% Keeping, dropping (with a certificate) and consuming goals

slice_term(slc(Kept, Dropped, Consumed, _, _), comp(sl, [KL, DL, CL])) :-
    maplist(int_t, Kept, KTs),
    list_t(KTs, KL),
    findall(comp(drop, [int(I), C]), member(I-C, Dropped), Ds),
    list_t(Ds, DL),
    maplist(int_t, Consumed, CTs),
    list_t(CTs, CL).

int_t(I, int(I)).

%  close_over(+Env, +Bound, +Ground, +Goals, +Demand, +Consumed, -Slice)
close_over(Env, Bound, Ground, Gs, Demand0, Consumed, slc(Kept, Dropped, Cons, Needs, Conflicts)) :-
    with_produced(Bound, Gs, Prods),
    ground_scan(Gs, Ground, Grounds),
    numbered_list(Prods, 1, NProds),
    maplist(annot, NProds, Grounds, Annotated),
    rev(Annotated, RevAnn),
    foldl(close_step(Env, Consumed), RevAnn, slc([], [], [], [], [])-Demand0, slc(Kept, Dropped, Cons, _, Conflicts)-DEnd),
    pairs_values(Prods, PVs),
    ord_union(PVs, ProdAll),
    ord_subtract(DEnd, ProdAll, Needs).

annot(Ix-(G-Prod), Gnd, a(Ix, G, Prod, Gnd)).

%  the ground set before each goal (scanl)
ground_scan([], _, []).
ground_scan([G|Gs], Gr, [Gr|Grs]) :-
    ground_after(Gr, G, Gr1),
    ground_scan(Gs, Gr1, Grs).

close_step(Env, Consumed, a(Ix, G, Prod, Gnd), slc(K, D, C, N, Cf)-Dem, Out) :-
    if_commit(term_member(G, Consumed),
              ( ord_intersection(Prod, Dem, PD), ord_union(Cf, PD, Cf1),
                Out = slc(K, D, [Ix|C], N, Cf1)-Dem ),
    if_commit(( ord_intersection(Prod, Dem, PD), PD \== [] ),
              ( local_vars(Env, G, LV), ord_union(Dem, LV, Dem1), Out = slc([Ix|K], D, C, N, Cf)-Dem1 ),
              ( Env = senv(Prog, _, _, _),
                totality(Prog, Gnd, Prod, G, MC),
                if_commit(MC = just(Cert),
                          Out = slc(K, [Ix-Cert|D], C, N, Cf)-Dem,
                          ( local_vars(Env, G, LV), ord_union(Dem, LV, Dem1), Out = slc([Ix|K], D, C, N, Cf)-Dem1 )) ))).

%  totality(+Prog, +Ground, +Produced, +Goal, -MaybeCert): a certificate
%  that a goal always succeeds exactly once and binds only the variables it
%  produces, given the variables ground before it.
totality(Prog, Gnd, Prod, G, M) :-
    totality_in(Prog, [], nothing, Gnd, Prod, G, M).

totality_in(Prog, Visiting, Self, Gnd, Prod, G, M) :-
    goal_key(G, MK),
    if_commit(( MK = just(Key), prog_lookup(Prog, Key, just(_)) ),
              user_total(Prog, Visiting, Self, Gnd, Prod, G, Key, M),
              if_commit(builtin_cert(G, Gnd, Prod, Rule),
                        M = just(comp(total, [atom(Rule)])),
                        M = nothing)).

%  semidet: the certificate rule for a built-in goal
builtin_cert(G, Gnd, Prod, Rule) :-
    if_commit(G == atom(true), Rule = true,
    if_commit(G == atom(nl), Rule = output,
    if_commit(( G = comp(F, [_]), memberchk(F, [write, print, writeln, writeq, write_canonical]) ), Rule = output,
    if_commit(( G = comp('=', [var(X, _), T]), fresh_in(X, T, Prod) ), Rule = fresh_unify,
    if_commit(( G = comp('=', [T, var(X, _)]), fresh_in(X, T, Prod) ), Rule = fresh_unify,
    if_commit(( G = comp(is, [var(X, _), E]), fresh_in(X, E, Prod), gnd_in(E, Gnd), arith_t(E) ), Rule = arith,
    if_commit(( G = comp(F, [A, var(X, _)]),
                memberchk(F, [atom_codes, atom_chars, atom_length, number_codes, number_chars,
                              upcase_atom, downcase_atom, atomic_list_concat]),
                gnd_in(A, Gnd), fresh_in(X, A, Prod) ), Rule = text,
    if_commit(( G = comp(atomic_list_concat, [L, Sp, var(X, _)]), gnd_in(L, Gnd), gnd_in(Sp, Gnd),
                fresh_in(X, comp(x, [L, Sp]), Prod) ), Rule = text,
    if_commit(( G = comp(char_code, [var(X, _), Code]), gnd_in(Code, Gnd), fresh_in(X, Code, Prod) ), Rule = text,
    if_commit(( G = comp(F, [A, B, var(X, _)]), memberchk(F, [atom_concat, string_concat]),
                gnd_in(A, Gnd), gnd_in(B, Gnd), fresh_in(X, comp(x, [A, B]), Prod) ), Rule = text,
    if_commit(( G = comp(append, [A, B, var(X, _)]), gnd_in(A, Gnd), fresh_in(X, comp(x, [A, B]), Prod) ), Rule = append,
    if_commit(( G = comp(length, [L, var(X, _)]), gnd_in(L, Gnd), fresh_in(X, L, Prod) ), Rule = length,
    if_commit(( G = comp(reverse, [L, var(X, _)]), gnd_in(L, Gnd), fresh_in(X, L, Prod) ), Rule = reverse,
              fail))))))))))))).

fresh_in(X, T, Prod) :-
    ord_memberchk(X, Prod),
    term_var_ids(T, TV),
    ord_nonmember(X, TV).

arith_t(T) :-
    if_commit(T = int(_), true,
    if_commit(T = var(_, _), true,
    if_commit(( T = comp(Op, [A, B]), memberchk(Op, ['+', '-', '*']) ), ( arith_t(A), arith_t(B) ),
    if_commit(T = comp('-', [A]), arith_t(A),
              fail)))).

user_total(Prog, Visiting, Self, Gnd, Prod, G, F/N, M) :-
    goal_args(G, As),
    numbered_list(As, 0, NAs),
    findall(I, ( member(I-A, NAs), gnd_in(A, Gnd) ), Ins),
    findall(A, ( member(I-A, NAs), not_memberchk(I, Ins) ), Outs),
    findall(V, ( member(I-A, NAs), memberchk(I, Ins), term_var_ids(A, Vs), member(V, Vs) ), InV0),
    sort(InV0, InVars),
    if_commit(( outs_fresh(Outs, Prod, InVars), total_ok(Self, F/N, Ins, As, Prog, Visiting) ),
              ( maplist(int_t, Ins, ITs), list_t(ITs, ModeT),
                M = just(comp(total, [comp(pred, [comp('/', [atom(F), int(N)]), ModeT])])) ),
              M = nothing).

outs_fresh(Outs, Prod, InVars) :-
    findall(X, ( member(O, Outs), O = var(X, _) ), Xs),
    same_length(Xs, Outs),
    sort(Xs, SXs),
    same_length(SXs, Xs),
    if_commit(( member(X, Xs), if_commit(( ord_memberchk(X, Prod), ord_nonmember(X, InVars) ), fail, true) ),
              fail, true).

total_ok(Self, Key, Ins, As, Prog, Visiting) :-
    if_commit(( Self = just(SK-SIns-SW-TailV), SK == Key ),
              ( Ins == SIns, SW1 is SW + 1, nth_det(SW1, As, just(var(X, _))), X =:= TailV ),
              ( not_memberchk(Key, Visiting), pred_total(Prog, [Key|Visiting], Key, Ins) )).

%  A predicate is total in a mode when it has one clause, or two clauses
%  that switch on an input list ([] and [H|T]), every other input head
%  argument is a distinct variable, and every body goal is total; a
%  recursive call must be on the tail T.
pred_total(Prog, Visiting, Key, Ins) :-
    prog_lookup(Prog, Key, just(Cls)),
    length(Cls, L),
    if_commit(L =:= 1,
              ( Cls = [C], input_vars_ok(C, Ins, -1), body_ok(Prog, Visiting, Key, Ins, C, nothing) ),
              ( L =:= 2, Cls = [C1, C2],
                once_det(( member(Sw, Ins),
                           if_commit(switch_ok(Prog, Visiting, Key, Ins, C1, C2, Sw), true,
                                     switch_ok(Prog, Visiting, Key, Ins, C2, C1, Sw)) )) )).

input_vars_ok(clause(H, _, _), Ins, Skip) :-
    goal_args(H, As),
    numbered_list(As, 0, NAs),
    findall(X, ( member(I-X, NAs), memberchk(I, Ins), I =\= Skip ), Xs),
    findall(V, member(var(V, _), Xs), Vs),
    same_length(Vs, Xs),
    sort(Vs, SVs),
    same_length(SVs, Vs).

switch_ok(Prog, Visiting, Key, Ins, CNil, CCons, Sw) :-
    CNil = clause(HN, _, _),
    CCons = clause(HC, _, _),
    goal_args(HN, ANs),
    goal_args(HC, ACs),
    Sw1 is Sw + 1,
    nth_det(Sw1, ANs, just(atom('[]'))),
    nth_det(Sw1, ACs, just(comp('.', [var(Hv, _), var(Tv, _)]))),
    Hv =\= Tv,
    input_vars_ok(CNil, Ins, Sw),
    input_vars_ok(CCons, Ins, Sw),
    numbered_list(ACs, 0, NACs),
    if_commit(( member(I-A, NACs), memberchk(I, Ins), I =\= Sw, term_var_ids(A, AV),
                if_commit(memberchk(Hv, AV), true, memberchk(Tv, AV)) ), fail, true),
    body_ok(Prog, Visiting, Key, Ins, CNil, nothing),
    body_ok(Prog, Visiting, Key, Ins, CCons, just(Sw-Tv)).

body_ok(Prog, Visiting, Key, Ins, clause(H, B, _), Sw) :-
    goal_args(H, As),
    numbered_list(As, 0, NAs),
    findall(Vs, ( member(I-A, NAs), memberchk(I, Ins), term_var_ids(A, Vs) ), VLs),
    ord_union(VLs, Gnd0),
    conj_list(B, Gs),
    if_commit(Sw = just(S1-Tv), Self = just(Key-Ins-S1-Tv), Self = nothing),
    body_goals_ok(Gs, Gnd0, Gnd0, Prog, Visiting, Self).

body_goals_ok([], _, _, _, _, _).
body_goals_ok([G|Gs], Gnd, Seen, Prog, Visiting, Self) :-
    term_var_ids(G, GV),
    ord_subtract(GV, Seen, Prod),
    totality_in(Prog, Visiting, Self, Gnd, Prod, G, just(_)),
    ground_after(Gnd, G, Gnd1),
    ord_union(Seen, GV, Seen1),
    body_goals_ok(Gs, Gnd1, Seen1, Prog, Visiting, Self).

% ---------------------------------------------------------------------------
% Helpers written into every generated file (cut-free).

helper_lines([
  "% plop2_nth_r(+K, +T, -R): R = c(E) for element K of a list, or character K",
  "% of an atom or integer; R = none if there is no such element.",
  "plop2_nth_r(K, T, R) :- ( plop2_nth_char(K, T, C) -> R = c(C) ; R = none ).",
  "plop2_nth_char(K, T, C) :-",
  "    (   is_list(T)",
  "    ->  nth1(K, T, C)",
  "    ;   integer(T)",
  "    ->  plop2_int_char(K, T, C)",
  "    ;   atom(T)",
  "    ->  B is K - 1, sub_atom(T, B, 1, _, C)",
  "    ).",
  "% Character K of an integer by formula: digit = (N // 10^(D-K)) mod 10.",
  "plop2_int_char(K, N, C) :-",
  "    (   N < 0",
  "    ->  (   K =:= 1 -> C = '-' ; K1 is K - 1, M is -N, plop2_int_char(K1, M, C) )",
  "    ;   plop2_ndigits(N, D), K >= 1, K =< D,",
  "        Digit is (N // 10 ^ (D - K)) mod 10,",
  "        Code is 0'0 + Digit, char_code(C, Code)",
  "    ).",
  "plop2_ndigits(N, D) :- ( N < 10 -> D = 1 ; M is N // 10, plop2_ndigits(M, D0), D is D0 + 1 ).",
  "% plop2_chain(+K, +Parts, -R): element K of the concatenation of the parts.",
  "% call(Part, J, RJ) gives element J of a part.  A part without element K has",
  "% L < K elements, and element K of the whole is element K - L of the rest.",
  "plop2_chain(_, [], none).",
  "plop2_chain(K, [P|Ps], R) :-",
  "    call(P, K, R0),",
  "    (   R0 = c(_)",
  "    ->  R = R0",
  "    ;   plop2_part_length(P, K, L), K1 is K - L, plop2_chain(K1, Ps, R)",
  "    ).",
  "plop2_part_length(P, K, L) :-",
  "    K1 is K - 1,",
  "    (   K1 =:= 0",
  "    ->  L = 0",
  "    ;   call(P, K1, R1), ( R1 = c(_) -> L = K1 ; plop2_part_length(P, K1, L) )",
  "    ).",
  "plop2_static(Es, J, R) :- plop2_nth_r(J, Es, R).",
  "plop2_value(V, J, R) :- plop2_nth_r(J, V, R).",
  "plop2_chain_c(Parts, J, R) :- plop2_chain(J, Parts, R)."
]).

helper_source(S) :-
    helper_lines(Ls),
    atomic_list_concat(Ls, '\n', A),
    atom_concat(A, '\n', A1),
    atom_string(A1, S).
