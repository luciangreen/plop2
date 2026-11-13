/*  plop_proof.pl - the independent checker for plop2 slice proofs.

    Every clause of a per-character program comes with a slice_step: the
    source clause, the result clause, which source goals were kept, dropped
    (each with a totality certificate) or consumed, and the derivation of
    the element expression.  This module re-checks each step with its own
    analyses (first occurrences, groundness, certificates, element rules)
    and does not use slice.pl.  It also regenerates the wrapper and
    dispatcher clauses, checks formula clauses by exhaustive evaluation,
    and checks input-character facts by symbolic evaluation.

    A failed condition is thrown as pp_fail(Message).
*/

pp_ensure(G, Msg) :-
    if_commit(G, true, throw(pp_fail(Msg))).

pp_fail(Msg) :-
    throw(pp_fail(Msg)).

pp_teq(A, B) :-
    same_term(A, B, true).

pp_show_key(F/N, S) :-
    format(string(S), "~w/~d", [F, N]).

proof_text(Steps, Text) :-
    findall(L, ( member(S, Steps), show_term_q(S, T), format(string(L), "~w.\n", [T]) ), Ls),
    atomic_list_concat(["% plop2 slice proof: one step per rewrite (see docs/proof_rules.md).\n"|Ls], A),
    atom_string(A, Text).

read_proof(Src, E) :-
    parse_program(Src, PE),
    if_commit(PE = right(P),
              ( program_clauses(P, KCs),
                findall(T, ( member(_-Cs, KCs), member(C, Cs), clause_term(C, T) ), Steps),
                E = right(Steps) ),
              E = PE).

% ---------------------------------------------------------------------------
% Names and templates (written independently of the generator)

pp_sp_name(spec(F/N, J, K), Name) :-
    N1 is N - 1,
    if_commit(J =:= N1,
              format(atom(Name), "~w__char~d", [F, K]),
              ( J1 is J + 1, format(atom(Name), "~w__a~d_char~d", [F, J1, K]) )).

pp_d_name(F/_, J, K, Name) :-
    J1 is J + 1,
    format(atom(Name), "~w__a~d_upto~d_r", [F, J1, K]).

pp_sp_of(T, Sp) :-
    if_commit(T = comp(spec, [comp('/', [atom(F), int(N)]), int(J), int(K)]),
              Sp = spec(F/N, J, K),
              ( show_term_q(T, S), string_concat("bad spec ", S, M), pp_fail(M) )).

pp_as_clause(T, C) :-
    max_var_id(T, MV),
    NV is MV + 1,
    if_commit(T = comp(':-', [H, B]),
              C = clause(H, B, NV),
              if_commit(is_callable_t(T, true),
                        C = clause(T, atom(true), NV),
                        ( show_term_q(T, S), string_concat("not a clause: ", S, M), pp_fail(M) ))).

pp_list_of(T, L) :-
    if_commit(T == atom('[]'), L = [],
              if_commit(T = comp('.', [H, Tl]),
                        ( pp_list_of(Tl, L0), L = [H|L0] ),
                        ( show_term_q(T, S), string_concat("not a list: ", S, Msg), pp_fail(Msg) ))).

pp_ints_of(T, Is) :-
    pp_list_of(T, Ts),
    if_commit(ints_of(Ts, Is0), Is = Is0, pp_fail("not an index")).

pp_head_vars(N, As) :-
    N1 is N - 1,
    findall(var(I, Nm), ( between(0, N1, I), I1 is I + 1, format(atom(Nm), "A~d", [I1]) ), As).

%  name__r(A.., R) :- once(name__alt(A.., R)).   name(A.., C) :- name__r(A.. c(C)).
wrapper_clauses(F/N, J, K, [C1, C2]) :-
    pp_sp_name(spec(F/N, J, K), Name),
    pp_head_vars(N, As),
    R = var(N, 'R'),
    N1 is N + 1,
    C = var(N1, 'C'),
    replace_nth0(As, J, R, ArgsR),
    replace_nth0(As, J, C, ArgsC),
    replace_nth0(As, J, comp(c, [C]), ArgsCR),
    atom_concat(Name, '__r', RN),
    atom_concat(Name, '__alt', AN),
    NV is N + 2,
    C1 = clause(comp(RN, ArgsR), comp(once, [comp(AN, ArgsR)]), NV),
    C2 = clause(comp(Name, ArgsC), comp(RN, ArgsCR), NV).

%  disp(Others.., J, R) :- ( J =:= 1 -> q__char1__r(..R..) ; ... ; R = none ).
dispatcher_clause(F/N, J, K, clause(comp(DN, HArgs), Body, NV)) :-
    pp_head_vars(N, As),
    other_args(As, J, Others),
    Jv = var(N, 'J'),
    N1 is N + 1,
    R = var(N1, 'R'),
    take(J, Others, Bf),
    drop(J, Others, Af),
    concat_lists([Bf, [R], Af], ArgsFor),
    findall(KK, between(1, K, KK), Ks),
    rev(Ks, RKs),
    foldl(disp_alt(F/N, J, Jv, ArgsFor), RKs, comp('=', [R, atom(none)]), Body),
    pp_d_name(F/N, J, K, DN),
    conc(Others, [Jv, R], HArgs),
    NV is N + 2.

disp_alt(Key, J, Jv, ArgsFor, KK, E, comp(';', [comp('->', [comp('=:=', [Jv, int(KK)]), comp(RN, ArgsFor)]), E])) :-
    pp_sp_name(spec(Key, J, KK), Name),
    atom_concat(Name, '__r', RN).

% ---------------------------------------------------------------------------
% Entry point

%  check_plop_proof(+Source, +Steps, +Generated, -Either)
check_plop_proof(Src, Steps, Gen, E) :-
    catch(( check_plop_proof_(Src, Steps, Gen, R), E = right(R) ),
          pp_fail(M),
          E = left(M)).

check_plop_proof_(Src, Steps, Gen, [Report]) :-
    findall(S, ( member(S, Steps), S = comp(slice_step, _) ), Slices),
    maplist(slice_spec_of, Slices, SpL),
    sort(SpL, Specs),
    maplist(result_clause, Slices, ResultClauses),
    Cx = ppcx(Src, Specs, ResultClauses),
    maplist(check_slice(Cx), Slices, Justified),
    findall(D, ( member(_-Ds, Justified), member(D, Ds) ), DL),
    sort(DL, DispNeeded),
    findall(W, ( member(spec(Key, J, K), Specs), wrapper_clauses(Key, J, K, Ws), member(W, Ws) ), Wrappers),
    findall(DC, ( member(t(Key, J, K), DispNeeded), dispatcher_clause(Key, J, K, DC) ), Disps),
    helper_program_copy(HP),
    prog_order(HP, HO),
    sort(HO, HelperKeys),
    findall(S, ( member(S, Steps), S = comp(formula_step, _) ), FSteps),
    maplist(check_formula(Gen), FSteps, FormulaCls),
    findall(S, ( member(S, Steps), S = comp(input_chars_step, _) ), ISteps),
    maplist(check_input_chars(Gen), ISteps, InputCls),
    findall(K, ( member(clause(H, _, _), FormulaCls), goal_key(H, just(K)) ), FK0),
    sort(FK0, FormulaKeys),
    findall(C, member(C-_, Justified), JCs),
    findall(W, ( member(W, Wrappers), W = clause(WH, _, _), goal_key(WH, just(WK)),
                 ord_nonmember(WK, FormulaKeys) ), Ws1),
    concat_lists([JCs, Ws1, Disps, FormulaCls, InputCls], Expected),
    pp_by_key(Expected, ByKey),
    prog_order(Src, SO),
    sort(SO, SourceKeys),
    program_clauses(Gen, GKCs),
    maplist(pp_coverage(ByKey, HelperKeys, SourceKeys, HP, Src), GKCs),
    map_keys(ByKey, BK),
    maplist(pp_in_generated(Gen), BK),
    length(Slices, NS),
    length(FormulaCls, NF),
    length(InputCls, NI),
    format(string(Report), "proof accepted: ~d slice steps, ~d formula steps, ~d input-character steps", [NS, NF, NI]).

slice_spec_of(S, Sp) :-
    if_commit(S = comp(slice_step, [St|_]), pp_sp_of(St, Sp), pp_fail("bad step")).

result_clause(S, Sp-C) :-
    if_commit(S = comp(slice_step, [St, _, _, ResT, _, _]),
              ( pp_sp_of(St, Sp), pp_as_clause(ResT, C) ),
              pp_fail("bad slice_step")).

%  the input positions a program reads, recomputed from its result clauses
pp_used_of(ppcx(_, _, RCs), Sp, Used) :-
    Sp = spec(_, J, _),
    findall(U, ( member(Sp1-C, RCs), Sp1 == Sp, used_params(J, C, U) ), Us),
    ord_union(Us, Used).

pp_by_key(Cls, Map) :-
    map_empty(E),
    foldl(pp_by_key_add, Cls, E, Map).

pp_by_key_add(C, M0, M) :-
    C = clause(H, _, _),
    goal_key(H, MK),
    if_commit(MK = just(K),
              ( map_find(M0, K, [], Old), conc(Old, [C], New), map_put(K, New, M0, M) ),
              M = M0).

pp_variant(A, B) :-
    clause_term(A, TA),
    clause_term(B, TB),
    empty_state(0, St),
    variant_t(St, TA, TB, true).

pp_coverage(ByKey, HelperKeys, SourceKeys, HP, Src, K-Cs) :-
    pp_show_key(K, KS),
    if_commit(ord_memberchk(K, HelperKeys),
              ( prog_lookup(HP, K, MR), maybe_default(MR, [], Ref),
                string_concat(KS, ": differs from the helper library", M),
                pp_ensure(( same_length(Cs, Ref), maplist(pp_variant, Cs, Ref) ), M) ),
    if_commit(ord_memberchk(K, SourceKeys),
              ( prog_lookup(Src, K, MR), maybe_default(MR, [], Ref),
                string_concat(KS, ": differs from the source", M),
                pp_ensure(( same_length(Cs, Ref), maplist(pp_variant, Cs, Ref) ), M) ),
              ( map_get(ByKey, K, MJ),
                if_commit(MJ = just(Js), true, ( string_concat("unjustified predicate ", KS, M0), pp_fail(M0) )),
                string_concat(KS, ": clause count differs from its proof", M1),
                pp_ensure(same_length(Js, Cs), M1),
                maplist(pp_same_clause(KS), Cs, Js) ))).

pp_same_clause(KS, A, B) :-
    if_commit(pp_variant(A, B), true,
              ( clause_term(A, TA), clause_term(B, TB), show_term_q(TA, SA), show_term_q(TB, SB),
                format(string(M), "~w: a clause differs from its proof:\n  program: ~w\n  proof:   ~w", [KS, SA, SB]),
                pp_fail(M) )).

pp_in_generated(Gen, K) :-
    pp_show_key(K, KS),
    string_concat("justified but missing: ", KS, M),
    pp_ensure(prog_lookup(Gen, K, just(_)), M).

%  the helpers are part of the language plop2 targets; they are compared
%  with this copy (see docs/proof_rules.md for their lemmas)
helper_program_copy(P) :-
    helper_copy_lines(Ls),
    atomic_list_concat(Ls, '\n', A),
    atom_string(A, S),
    parse_program(S, PE),
    if_commit(PE = right(P0), P = P0, empty_program(P)).

helper_copy_lines([
  "plop2_nth_r(K, T, R) :- ( plop2_nth_char(K, T, C) -> R = c(C) ; R = none ).",
  "plop2_nth_char(K, T, C) :- ( is_list(T) -> nth1(K, T, C) ; integer(T) -> plop2_int_char(K, T, C) ; atom(T) -> B is K - 1, sub_atom(T, B, 1, _, C) ).",
  "plop2_int_char(K, N, C) :- ( N < 0 -> ( K =:= 1 -> C = '-' ; K1 is K - 1, M is -N, plop2_int_char(K1, M, C) ) ; plop2_ndigits(N, D), K >= 1, K =< D, Digit is (N // 10 ^ (D - K)) mod 10, Code is 0'0 + Digit, char_code(C, Code) ).",
  "plop2_ndigits(N, D) :- ( N < 10 -> D = 1 ; M is N // 10, plop2_ndigits(M, D0), D is D0 + 1 ).",
  "plop2_chain(_, [], none).",
  "plop2_chain(K, [P|Ps], R) :- call(P, K, R0), ( R0 = c(_) -> R = R0 ; plop2_part_length(P, K, L), K1 is K - L, plop2_chain(K1, Ps, R) ).",
  "plop2_part_length(P, K, L) :- K1 is K - 1, ( K1 =:= 0 -> L = 0 ; call(P, K1, R1), ( R1 = c(_) -> L = K1 ; plop2_part_length(P, K1, L) ) ).",
  "plop2_static(Es, J, R) :- plop2_nth_r(J, Es, R).",
  "plop2_value(V, J, R) :- plop2_nth_r(J, V, R).",
  "plop2_chain_c(Parts, J, R) :- plop2_chain(J, Parts, R)."
]).

% ---------------------------------------------------------------------------
% Slices.  A scope is scope(Goals, Bound, Ground).

check_slice(Cx, S, Res-Disp) :-
    if_commit(S = comp(slice_step, [St, int(I), SrcT, ResT, SlT, Node]), true, pp_fail("bad slice_step")),
    pp_sp_of(St, Sp),
    Sp = spec(Key, J, K),
    pp_as_clause(SrcT, Src),
    pp_as_clause(ResT, Res),
    pp_sp_name(Sp, SpN),
    format(string(Here), "~w clause ~d: ", [SpN, I]),
    Cx = ppcx(SrcProg, _, _),
    prog_lookup(SrcProg, Key, MB),
    maybe_default(MB, [], BaseCls),
    length(BaseCls, LB),
    pp_need(( I >= 1, I =< LB ), Here, "no such source clause"),
    nth_det(I, BaseCls, just(Base)),
    pp_need(pp_variant(Base, Src), Here, "not the source clause"),
    Src = clause(SH, SB, _),
    goal_args(SH, Args),
    other_args(Args, J, Inputs),
    maplist(term_var_ids, Inputs, IVs),
    ord_union(IVs, Bound0),
    clause_term(Src, SrcCT),
    term_var_ids(SrcCT, SrcVars),
    conj_list(SB, Gs),
    Top = scope(Gs, Bound0, Bound0),
    Res = clause(RH, E, _),
    atom_concat(SpN, '__alt', AN),
    if_commit(( RH = comp(AN, RArgs), same_length(RArgs, Args) ), true,
              ( wmsg(Here, "wrong head", M0), pp_fail(M0) )),
    J1 is J + 1,
    nth_det(J1, RArgs, just(R)),
    pp_need(inputs_same(Args, RArgs, J), Here, "inputs differ"),
    pp_need(is_fresh_in(SrcVars, R), Here, "the result variable is not fresh"),
    slice_of(SlT, Kept, Dropped, ConsumedIx),
    length(Gs, LG),
    check_partition(Here, LG, Kept, Dropped, ConsumedIx),
    check_certs(Here, SrcProg, Top, Dropped),
    pick_kept(Kept, Gs, KeptGoals),
    pp_need(node_goal(Node, just(_)), Here, "bad derivation"),
    node_goal(Node, just(EGoal)),
    conc(KeptGoals, [EGoal], WantGs),
    mk_conj(WantGs, WantE),
    pp_need(pp_teq(E, WantE), Here, "body is not the kept goals followed by the element expression"),
    nth_det(J1, Args, just(Subj)),
    check_node(Cx, Here, SrcVars, Top, Subj, K, R, Node, nr(NCons, NNeeds, NFresh, Disp)),
    pick_kept(ConsumedIx, Gs, ConsumedGoals),
    pp_need(same_shown(NCons, ConsumedGoals), Here, "consumed goals differ from the derivation's producers"),
    with_produced(Bound0, Gs, Prods),
    numbered_list(Prods, 1, NProds),
    findall(P, ( member(Ix-(_-P), NProds), memberchk(Ix, Kept) ), PKs),
    ord_union([Bound0|PKs], Readable),
    pp_need(ord_subset(NNeeds, Readable), Here, "the element expression reads a variable no kept goal binds"),
    findall(P, ( member(Ix-(_-P), NProds), memberchk(Ix, ConsumedIx) ), PCs),
    ord_union(PCs, ProdConsumed),
    maplist(term_var_ids, KeptGoals, KVs),
    ord_union(KVs, KeptVars),
    pp_need(ord_intersection(ProdConsumed, KeptVars, []), Here, "a kept goal reads a variable of a consumed goal"),
    pp_need(distinct_ids_p(NFresh), Here, "a fresh variable is introduced twice").

wmsg(Here, Msg, M) :-
    string_concat(Here, Msg, M).

pp_need(G, Here, Msg) :-
    wmsg(Here, Msg, M),
    pp_ensure(G, M).

inputs_same(Args, RArgs, J) :-
    numbered_list(Args, 0, NAs),
    if_commit(( member(Ix-A, NAs), Ix =\= J, Ix1 is Ix + 1, nth_det(Ix1, RArgs, just(B)),
                if_commit(pp_teq(A, B), fail, true) ),
              fail, true).

is_fresh_in(SrcVars, T) :-
    T = var(I, _),
    ord_nonmember(I, SrcVars).

distinct_ids_p(Ids) :-
    msort(Ids, S),
    sort(Ids, S1),
    same_length(S, S1).

same_shown(As, Bs) :-
    maplist(show_term_q, As, SA),
    maplist(show_term_q, Bs, SB),
    sort(SA, S1),
    sort(SB, S2),
    S1 == S2.

node_goal(N, M) :-
    if_commit(N = comp(e, [_, _, _, _, G, _, _]), M = just(G), M = nothing).

slice_of(T, Kept, Dropped, Consumed) :-
    if_commit(T = comp(sl, [KT, DT, CT]),
              ( pp_ints_of(KT, Kept),
                pp_list_of(DT, Ds),
                maplist(drop_of, Ds, Dropped),
                pp_ints_of(CT, Consumed) ),
              ( show_term_q(T, S), string_concat("bad slice ", S, M), pp_fail(M) )).

drop_of(D, I-Cert) :-
    if_commit(D = comp(drop, [int(I0), C0]), ( I = I0, Cert = C0 ), pp_fail("bad drop")).

check_partition(Here, N, Kept, Dropped, Consumed) :-
    pairs_keys(Dropped, DIx),
    concat_lists([Kept, DIx, Consumed], All),
    findall(I, between(1, N, I), Want),
    sort(All, SAll),
    pp_need(( length(All, N), SAll == Want ), Here, "every goal must be kept, dropped with a certificate, or consumed").

%  Groundness (the checker's own copy of the rules).
pp_g_after(Gr, G, Gr1) :-
    if_commit(( G = comp('=', [A, B]), pp_gnd(A, Gr) ),
              ( term_var_ids(B, BV), ord_union(Gr, BV, Gr1) ),
    if_commit(( G = comp('=', [A, B]), pp_gnd(B, Gr) ),
              ( term_var_ids(A, AV), ord_union(Gr, AV, Gr1) ),
    if_commit(( G = comp(is, [X, E]), pp_gnd(E, Gr) ),
              ( term_var_ids(X, XV), ord_union(Gr, XV, Gr1) ),
    if_commit(( G = comp(F, As), As = [_|_], length(As, N), key_atom(F, N, KA),
                pp_fun(Fun), memberchk(KA, Fun), init_of(As, Init), pp_all_gnd(Init, Gr) ),
              ( last_of(As, L), term_var_ids(L, LV), ord_union(Gr, LV, Gr1) ),
    if_commit(( G = comp(F, As), As = [_|_], length(As, N), key_atom(F, N, KA),
                pp_rev(Rev), memberchk(KA, Rev), last_of(As, L), pp_gnd(L, Gr) ),
              ( init_of(As, Init), maplist(term_var_ids, Init, IVs), ord_union([Gr|IVs], Gr1) ),
              Gr1 = Gr))))).

pp_gnd(T, Gr) :-
    term_var_ids(T, V),
    ord_subset(V, Gr).

pp_all_gnd([], _).
pp_all_gnd([T|Ts], Gr) :-
    pp_gnd(T, Gr),
    pp_all_gnd(Ts, Gr).

pp_fun(['atom_codes/2', 'atom_chars/2', 'number_codes/2', 'number_chars/2',
        'atom_length/2', 'char_code/2', 'upcase_atom/2', 'downcase_atom/2',
        'atomic_list_concat/2', 'atomic_list_concat/3', 'atom_concat/3',
        'string_concat/3', 'string_chars/2', 'atom_string/2',
        'append/3', 'reverse/2', 'length/2', 'nth0/3', 'nth1/3',
        'last/2', 'sum_list/2', 'max_list/2', 'min_list/2', 'msort/2', 'sort/2',
        'succ/2', 'plus/3']).

pp_rev(['atom_codes/2', 'atom_chars/2', 'char_code/2', 'string_chars/2']).

pp_g_after_f(G, Gr, Gr1) :-
    pp_g_after(Gr, G, Gr1).

ground_before(scope(Gs, _, Gr), Ix, GB) :-
    Ix1 is Ix - 1,
    take(Ix1, Gs, Before),
    foldl(pp_g_after_f, Before, Gr, GB).

%  Re-check every totality certificate.
check_certs(Here, Prog, Sc, Dropped) :-
    maplist(check_cert(Here, Prog, Sc), Dropped).

check_cert(Here, Prog, Sc, Ix-Cert) :-
    Sc = scope(Gs, Bound, _),
    nth_det(Ix, Gs, just(G)),
    with_produced(Bound, Gs, Prods),
    nth_det(Ix, Prods, just(_-Prod)),
    ground_before(Sc, Ix, Gnd),
    goal_key(G, MK),
    if_commit(( MK = just(GK), prog_lookup(Prog, GK, just(_)) ), UD = true, UD = false),
    show_term_q(G, GS),
    format(string(M), "~wgoal ~d (~w) is dropped without a valid totality certificate", [Here, Ix, GS]),
    pp_ensure(cert_ok(Cert, MK, UD, G, Prod, Gnd, Prog), M).

cert_ok(Cert, MK, UD, G, Prod, Gnd, Prog) :-
    if_commit(( Cert = comp(total, [comp(pred, [comp('/', [atom(F), int(N)]), ModeT])]), MK = just(F1/N1),
                F1 == F, N1 =:= N, UD == true, static_list(ModeT, just(MTs)), ints_of(MTs, Ins) ),
              ( call_mode_ok(Ins, G, Prod, Gnd), total_pred(Prog, [], F/N, Ins) ),
              ( UD == false, builtin_cert_ok(Cert, G, Gnd, Prod) )).

builtin_cert_ok(Cert, G, Gnd, Prod) :-
    Cert = comp(total, [atom(Rule)]),
    if_commit(( Rule == true, G == atom(true) ), true,
    if_commit(( Rule == output, G == atom(nl) ), true,
    if_commit(( Rule == output, G = comp(F, [_]) ), memberchk(F, [write, print, writeln, writeq, write_canonical]),
    if_commit(( Rule == fresh_unify, G = comp('=', [A, B]) ),
              if_commit(( A = var(X, _), pp_fresh_v(X, B, Prod) ), true, ( B = var(X2, _), pp_fresh_v(X2, A, Prod) )),
    if_commit(( Rule == arith, G = comp(is, [var(X, _), E]) ), ( pp_fresh_v(X, E, Prod), pp_gnd(E, Gnd), pp_arith(E) ),
    if_commit(( Rule == text, G = comp(char_code, [var(X, _), Code]) ), ( pp_gnd(Code, Gnd), pp_fresh_v(X, Code, Prod) ),
    if_commit(( Rule == text, G = comp(F, [A, var(X, _)]) ),
              ( memberchk(F, [atom_codes, atom_chars, atom_length, number_codes, number_chars, upcase_atom, downcase_atom, atomic_list_concat]),
                pp_gnd(A, Gnd), pp_fresh_v(X, A, Prod) ),
    if_commit(( Rule == text, G = comp(atomic_list_concat, [L, Sp, var(X, _)]) ),
              ( pp_gnd(L, Gnd), pp_gnd(Sp, Gnd), pp_fresh_v(X, comp(x, [L, Sp]), Prod) ),
    if_commit(( Rule == text, G = comp(F, [A, B, var(X, _)]) ),
              ( memberchk(F, [atom_concat, string_concat]), pp_gnd(A, Gnd), pp_gnd(B, Gnd), pp_fresh_v(X, comp(x, [A, B]), Prod) ),
    if_commit(( Rule == append, G = comp(append, [A, B, var(X, _)]) ), ( pp_gnd(A, Gnd), pp_fresh_v(X, comp(x, [A, B]), Prod) ),
    if_commit(( Rule == length, G = comp(length, [L, var(X, _)]) ), ( pp_gnd(L, Gnd), pp_fresh_v(X, L, Prod) ),
    if_commit(( Rule == reverse, G = comp(reverse, [L, var(X, _)]) ), ( pp_gnd(L, Gnd), pp_fresh_v(X, L, Prod) ),
              fail)))))))))))).

pp_fresh_v(X, T, Prod) :-
    ord_memberchk(X, Prod),
    term_var_ids(T, TV),
    ord_nonmember(X, TV).

pp_arith(T) :-
    if_commit(T = int(_), true,
    if_commit(T = var(_, _), true,
    if_commit(( T = comp(Op, [A, B]), memberchk(Op, ['+', '-', '*']) ), ( pp_arith(A), pp_arith(B) ),
    if_commit(T = comp('-', [A]), pp_arith(A),
              fail)))).

%  A call in a mode: the input positions are ground, the others are
%  distinct variables that first occur here and not in the inputs.
call_mode_ok(Ins, G, Prod, Gnd) :-
    goal_args(G, As),
    length(As, L),
    numbered_list(As, 0, NAs),
    if_commit(( member(I, Ins), if_commit(( I < L, I1 is I + 1, nth_det(I1, As, just(A)), pp_gnd(A, Gnd) ), fail, true) ),
              fail, true),
    findall(Vs, ( member(I-A, NAs), memberchk(I, Ins), term_var_ids(A, Vs) ), IVLs),
    ord_union(IVLs, InVars),
    findall(A, ( member(I-A, NAs), not_memberchk(I, Ins) ), Outs),
    findall(X, member(var(X, _), Outs), Xs),
    same_length(Xs, Outs),
    sort(Xs, SXs),
    same_length(SXs, Xs),
    if_commit(( member(X, Xs), if_commit(( ord_memberchk(X, Prod), ord_nonmember(X, InVars) ), fail, true) ),
              fail, true).

%  Totality of a predicate in a mode (rule TOTAL).
total_pred(Prog, Visiting, Key, Ins) :-
    not_memberchk(Key, Visiting),
    prog_lookup(Prog, Key, just(Cls)),
    length(Cls, L),
    if_commit(L =:= 1,
              ( Cls = [C], plain_inputs(C, Ins, -1), tp_body(Prog, Visiting, Key, Ins, C, nothing) ),
              ( L =:= 2, Cls = [A, B],
                once_det(( member(I, Ins),
                           if_commit(tp_sw(Prog, Visiting, Key, Ins, A, B, I), true,
                                     tp_sw(Prog, Visiting, Key, Ins, B, A, I)) )) )).

plain_inputs(clause(H, _, _), Ins, Skip) :-
    goal_args(H, As),
    numbered_list(As, 0, NAs),
    findall(X, ( member(I-X, NAs), memberchk(I, Ins), I =\= Skip ), Xs),
    findall(V, member(var(V, _), Xs), Vs),
    same_length(Vs, Xs),
    sort(Vs, SVs),
    same_length(SVs, Vs).

tp_sw(Prog, Visiting, Key, Ins, CN, CC, I) :-
    CN = clause(HN, _, _),
    CC = clause(HC, _, _),
    goal_args(HN, ANs),
    goal_args(HC, ACs),
    I1 is I + 1,
    nth_det(I1, ANs, just(atom('[]'))),
    nth_det(I1, ACs, just(comp('.', [var(Hv, _), var(Tv, _)]))),
    Hv =\= Tv,
    plain_inputs(CN, Ins, I),
    plain_inputs(CC, Ins, I),
    numbered_list(ACs, 0, NACs),
    if_commit(( member(Jx-X, NACs), memberchk(Jx, Ins), Jx =\= I, term_var_ids(X, XV),
                if_commit(memberchk(Hv, XV), true, memberchk(Tv, XV)) ), fail, true),
    tp_body(Prog, Visiting, Key, Ins, CN, nothing),
    tp_body(Prog, Visiting, Key, Ins, CC, just(I-Tv)).

tp_body(Prog, Visiting, Key, Ins, clause(H, B, _), Rec) :-
    goal_args(H, As),
    numbered_list(As, 0, NAs),
    findall(Vs, ( member(I-X, NAs), memberchk(I, Ins), term_var_ids(X, Vs) ), VLs),
    ord_union(VLs, Gnd0),
    conj_list(B, Gs),
    tp_goals(Gs, Gnd0, Gnd0, Prog, Visiting, Key, Ins, Rec).

tp_goals([], _, _, _, _, _, _, _).
tp_goals([G|Gs], Gnd, Seen, Prog, Visiting, Key, Ins, Rec) :-
    term_var_ids(G, GV),
    ord_subtract(GV, Seen, Prod),
    tp_goal_total(G, Gnd, Prod, Prog, Visiting, Key, Ins, Rec),
    pp_g_after(Gnd, G, Gnd1),
    ord_union(Seen, GV, Seen1),
    tp_goals(Gs, Gnd1, Seen1, Prog, Visiting, Key, Ins, Rec).

tp_goal_total(G, Gnd, Prod, Prog, Visiting, Key, Ins, Rec) :-
    goal_key(G, MK),
    if_commit(( MK = just(K), K == Key, Rec = just(I-Tv) ),
              ( call_mode_ok(Ins, G, Prod, Gnd), goal_args(G, As), I1 is I + 1,
                nth_det(I1, As, just(var(X, _))), X =:= Tv ),
              if_commit(( MK = just(K), prog_lookup(Prog, K, just(_)) ),
                        ( goal_args(G, As), numbered_list(As, 0, NAs),
                          findall(J, ( member(J-A, NAs), pp_gnd(A, Gnd) ), Ins1),
                          call_mode_ok(Ins1, G, Prod, Gnd),
                          total_pred(Prog, [Key|Visiting], K, Ins1) ),
                        builtin_total(Gnd, Prod, G))).

%  The built-in totality rules (the same list as for dropped goals).
builtin_total(Gnd, Prod, G) :-
    if_commit(G == atom(true), true,
    if_commit(G == atom(nl), true,
    if_commit(( G = comp(F, [_]), memberchk(F, [write, print, writeln, writeq, write_canonical]) ), true,
    if_commit(( G = comp('=', [var(X, _), T]), pp_fresh_v(X, T, Prod) ), true,
    if_commit(( G = comp('=', [T, var(X, _)]), pp_fresh_v(X, T, Prod) ), true,
    if_commit(G = comp(is, [var(X, _), E]), ( pp_fresh_v(X, E, Prod), pp_gnd(E, Gnd), pp_arith(E) ),
    if_commit(G = comp(char_code, [var(X, _), Code]), ( pp_gnd(Code, Gnd), pp_fresh_v(X, Code, Prod) ),
    if_commit(( G = comp(F, [A, var(X, _)]),
                memberchk(F, [atom_codes, atom_chars, atom_length, number_codes, number_chars,
                              upcase_atom, downcase_atom, atomic_list_concat]) ),
              ( pp_gnd(A, Gnd), pp_fresh_v(X, A, Prod) ),
    if_commit(G = comp(atomic_list_concat, [L, Sp, var(X, _)]),
              ( pp_gnd(L, Gnd), pp_gnd(Sp, Gnd), pp_fresh_v(X, comp(x, [L, Sp]), Prod) ),
    if_commit(( G = comp(F, [A, B, var(X, _)]), memberchk(F, [atom_concat, string_concat]) ),
              ( pp_gnd(A, Gnd), pp_gnd(B, Gnd), pp_fresh_v(X, comp(x, [A, B]), Prod) ),
    if_commit(G = comp(append, [A, B, var(X, _)]), ( pp_gnd(A, Gnd), pp_fresh_v(X, comp(x, [A, B]), Prod) ),
    if_commit(G = comp(length, [L, var(X, _)]), ( pp_gnd(L, Gnd), pp_fresh_v(X, L, Prod) ),
    if_commit(G = comp(reverse, [L, var(X, _)]), ( pp_gnd(L, Gnd), pp_fresh_v(X, L, Prod) ),
              fail))))))))))))).

% ---------------------------------------------------------------------------
% Element derivations.  A result is nr(Consumed, Needs, Fresh, Disp).

nr_empty(nr([], [], [], [])).

nr_concat(NRs, nr(C, N, F, D)) :-
    findall(X, ( member(nr(Cs, _, _, _), NRs), member(X, Cs) ), C),
    findall(X, member(nr(_, X, _, _), NRs), Ns),
    ord_union(Ns, N),
    findall(X, ( member(nr(_, _, Fs, _), NRs), member(X, Fs) ), F),
    findall(X, ( member(nr(_, _, _, Ds), NRs), member(X, Ds) ), D).

producer_in(scope(Gs, Bound, _), V, M) :-
    with_produced(Bound, Gs, Prods),
    numbered_list(Prods, 1, NProds),
    if_commit(( member(Ix-(G-P), NProds), ord_memberchk(V, P) ), M = just(Ix-G), M = nothing).

scope_before(scope(Gs, B, Gr), Ix, scope(Gs1, B, Gr)) :-
    Ix1 is Ix - 1,
    take(Ix1, Gs, Gs1).

pp_take_chars(N, S, T) :-
    string_length(S, L),
    if_commit(L =< N, T = S, sub_string_first(S, N, T)).

sub_string_first(S, N, T) :-
    string_chars(S, Cs),
    take(N, Cs, Cs1),
    string_chars(T, Cs1).

pp_needs_of(SrcVars, T, N) :-
    term_var_ids(T, V),
    ord_intersection(V, SrcVars, N).

pp_fresh_vars(H, SrcVars, Ts, Ids) :-
    pp_need(maplist(is_fresh_in(SrcVars), Ts), H, "a new variable is not fresh"),
    findall(I, member(var(I, _), Ts), Ids).

pp_sub0(H, Subs, S0) :-
    if_commit(Subs = [X|_], S0 = X, ( wmsg(H, "missing sub-derivation", M), pp_fail(M) )).

pp_node_goal_is(S0, Goal) :-
    node_goal(S0, just(G0)),
    pp_teq(G0, Goal).

%  check_node(+Cx, +Here, +SrcVars, +Scope, +Subject, +K, +R, +Node, -NR)
check_node(Cx, Here, SrcVars, Sc, Subject, K, R, Node, NR) :-
    if_commit(Node = comp(e, [atom(Rule), Subj, int(KK), R1, Goal, SubsT, Info]),
              ( pp_list_of(SubsT, Subs),
                show_term_q(Subject, SS),
                pp_take_chars(80, SS, SS80),
                format(string(H), "~w~w for element ~d of ~w: ", [Here, Rule, K, SS80]),
                pp_need(( pp_teq(Subj, Subject), KK =:= K, pp_teq(R1, R) ), H, "node is for another element"),
                N = nd(Cx, Here, SrcVars, Sc, Subject, K, R, H, Goal, Subs, Info),
                if_commit(node_rule_known(Rule),
                          node_rule(Rule, N, NR),
                          ( wmsg(H, "unknown rule", M), pp_fail(M) )) ),
              ( show_term_q(Node, NS), pp_take_chars(100, NS, NS100),
                format(string(M), "~wnot a derivation node: ~w", [Here, NS100]),
                pp_fail(M) )).

node_rule_known(Rule) :-
    memberchk(Rule, [el_head, el_tail, el_none, el_const, el_nth, el_unify, el_alias,
                     el_same_text, el_codes_of_text, el_text_of_codes, el_number_codes,
                     el_number_chars, el_reverse, el_maplist, el_spec, el_chain,
                     el_chain_const, el_branch]).

nd_fail(nd(_, _, _, _, _, _, _, H, _, _, _), Msg) :-
    wmsg(H, Msg, M),
    pp_fail(M).

nd_need(nd(_, _, _, _, _, _, _, H, _, _, _), G, Msg) :-
    pp_need(G, H, Msg).

nd_is_subj(nd(_, _, _, _, Subject, _, _, _, _, _, _), X) :-
    pp_teq(X, Subject).

%  the producer of the subject variable in this scope
nd_producer(N, Ix, G) :-
    N = nd(_, _, _, Sc, Subject, _, _, _, _, _, Info),
    if_commit(Info = comp(branch, [G0|_]), Recorded = G0, Recorded = Info),
    if_commit(Subject = var(V, _),
              ( producer_in(Sc, V, MP),
                if_commit(( MP = just(Ix0-G1), pp_teq(G1, Recorded) ),
                          ( Ix = Ix0, G = G1 ),
                          nd_fail(N, "the recorded goal is not the first producer of the subject")) ),
              nd_fail(N, "subject is not a variable")).

nd_template(N, S0) :-
    N = nd(_, _, _, _, _, _, _, _, Goal, _, _),
    nd_need(N, pp_node_goal_is(S0, Goal), "template").

nd_recurse(N, Sc1, T, K1, R1, S0, NR) :-
    N = nd(Cx, Here, SrcVars, _, _, _, _, _, _, _, _),
    check_node(Cx, Here, SrcVars, Sc1, T, K1, R1, S0, NR).

nr_add_consumed(G, nr(C, Nd, F, D), nr([G|C], Nd, F, D)).

node_rule(el_head, N, NR) :-
    N = nd(_, _, SrcVars, _, Subject, K, R, _, Goal, _, _),
    if_commit(( Subject = comp('.', [Hd, _]), K =:= 1 ),
              ( nd_need(N, pp_teq(Goal, comp('=', [R, comp(c, [Hd])])), "template"),
                pp_needs_of(SrcVars, Hd, Nd),
                NR = nr([], Nd, [], []) ),
              nd_fail(N, "not a list cell")).
node_rule(el_tail, N, NR) :-
    N = nd(_, _, _, Sc, Subject, K, R, H, _, Subs, _),
    if_commit(( Subject = comp('.', [_, Tl]), K > 1 ),
              ( pp_sub0(H, Subs, S0),
                nd_template(N, S0),
                K1 is K - 1,
                nd_recurse(N, Sc, Tl, K1, R, S0, NR) ),
              nd_fail(N, "not a list cell")).
node_rule(el_none, N, NR) :-
    N = nd(_, _, _, Sc, Subject, K, R, _, Goal, _, _),
    nd_need(N, pp_teq(Goal, comp('=', [R, atom(none)])), "template"),
    nd_need(N, none_ok(Sc, Subject, K), "the subject may have an element here"),
    nr_empty(NR).
node_rule(el_const, N, NR) :-
    N = nd(_, _, _, _, Subject, K, R, _, Goal, _, _),
    if_commit(( subject_text(Subject, Cs), length(Cs, L), K =< L ),
              ( nth_det(K, Cs, just(C)),
                nd_need(N, pp_teq(Goal, comp('=', [R, comp(c, [atom(C)])])), "template"),
                nr_empty(NR) ),
              nd_fail(N, "not a constant with this element")).
node_rule(el_nth, N, NR) :-
    N = nd(_, _, SrcVars, _, Subject, K, R, _, Goal, _, _),
    nd_need(N, pp_teq(Goal, comp(plop2_nth_r, [int(K), Subject, R])), "template"),
    pp_needs_of(SrcVars, Subject, Nd),
    NR = nr([], Nd, [], []).
node_rule(el_unify, N, NR) :-
    N = nd(_, _, _, Sc, _, K, R, H, _, Subs, _),
    nd_producer(N, Ix, G),
    if_commit(( G = comp('=', [X, T0]), nd_is_subj(N, X) ), T = T0,
              if_commit(( G = comp('=', [T0, X]), nd_is_subj(N, X) ), T = T0,
                        nd_fail(N, "producer is not a unification"))),
    pp_sub0(H, Subs, S0),
    nd_template(N, S0),
    scope_before(Sc, Ix, Sc1),
    nd_recurse(N, Sc1, T, K, R, S0, NR0),
    nr_add_consumed(G, NR0, NR).
node_rule(el_alias, N, NR) :-
    N = nd(_, _, _, Sc, _, K, R, H, _, Subs, _),
    nd_producer(N, Ix, G),
    if_commit(( G = comp('=', [X, Y]), Y = var(_, _), nd_is_subj(N, X) ), W = Y,
              if_commit(( G = comp('=', [Y, X]), Y = var(_, _), nd_is_subj(N, X) ), W = Y,
                        nd_fail(N, "producer is not an alias"))),
    Sc = scope(Gs, Bound, Gr),
    Ix1 is Ix - 1,
    take(Ix1, Gs, Before),
    maplist(term_var_ids, Before, BVs),
    ord_union([Bound|BVs], SeenBefore),
    W = var(WId, _),
    nd_need(N, ord_nonmember(WId, SeenBefore), "the alias's other variable occurs earlier"),
    pp_sub0(H, Subs, S0),
    nd_template(N, S0),
    drop(Ix, Gs, After),
    conc(Before, After, Gs1),
    nd_recurse(N, scope(Gs1, Bound, Gr), W, K, R, S0, NR0),
    nr_add_consumed(G, NR0, NR).
node_rule(el_same_text, N, NR) :-
    N = nd(_, _, _, Sc, _, K, R, H, _, Subs, _),
    nd_producer(N, Ix, G),
    if_commit(( G = comp(F, [A, X]), memberchk(F, [atom_chars, string_chars, atom_string]), nd_is_subj(N, X) ), T = A,
              if_commit(( G = comp(F, [X, L]), memberchk(F, [atom_chars, string_chars]), nd_is_subj(N, X) ), T = L,
                        nd_fail(N, "producer"))),
    pp_sub0(H, Subs, S0),
    nd_template(N, S0),
    scope_before(Sc, Ix, Sc1),
    nd_recurse(N, Sc1, T, K, R, S0, NR0),
    nr_add_consumed(G, NR0, NR).
node_rule(el_codes_of_text, N, NR) :-
    codes_rule(el_codes_of_text, N, NR).
node_rule(el_text_of_codes, N, NR) :-
    codes_rule(el_text_of_codes, N, NR).
node_rule(el_number_codes, N, NR) :-
    N = nd(_, _, SrcVars, _, _, K, R, H, Goal, _, _),
    nd_producer(N, _, G),
    if_commit(( G = comp(number_codes, [Num0, X]), nd_is_subj(N, X) ), Num = Num0, nd_fail(N, "producer")),
    if_commit(( Goal = comp(',', [comp(plop2_nth_r, [int(K1), N1, R0]),
                                  comp(';', [comp('->', [comp('=', [R01, comp(c, [Ch])]),
                                                         comp(',', [comp(char_code, [Ch1, Code]),
                                                                    comp('=', [R2, comp(c, [Code1])])])]),
                                             comp('=', [R3, atom(none)])])]),
                K1 =:= K, pp_teq(N1, Num), pp_teq(R01, R0), pp_teq(Ch1, Ch), pp_teq(Code1, Code),
                pp_teq(R2, R), pp_teq(R3, R) ),
              ( pp_fresh_vars(H, SrcVars, [R0, Ch, Code], Fr),
                pp_needs_of(SrcVars, Num, Nd),
                NR = nr([G], Nd, Fr, []) ),
              nd_fail(N, "template")).
node_rule(el_number_chars, N, NR) :-
    N = nd(_, _, SrcVars, _, _, K, R, _, Goal, _, _),
    nd_producer(N, _, G),
    if_commit(( G = comp(number_chars, [Num0, X]), nd_is_subj(N, X) ), Num = Num0,
              if_commit(( G = comp(atom_number, [X, Num0]), nd_is_subj(N, X) ), Num = Num0,
                        nd_fail(N, "producer"))),
    nd_need(N, pp_teq(Goal, comp(plop2_nth_r, [int(K), Num, R])), "template"),
    pp_needs_of(SrcVars, Num, Nd),
    NR = nr([G], Nd, [], []).
node_rule(el_reverse, N, NR) :-
    N = nd(_, _, SrcVars, _, _, K, R, H, Goal, _, _),
    nd_producer(N, _, G),
    if_commit(( G = comp(reverse, [L0, X]), nd_is_subj(N, X) ), L = L0, nd_fail(N, "producer")),
    conj_list(Goal, GL),
    if_commit(( GL = [comp(length, [L1, Len]),
                      comp(is, [Ix, comp('+', [comp('-', [Len1, int(K1)]), int(1)])]),
                      comp(';', [comp('->', [comp('>=', [Ix1, int(1)]),
                                             comp(',', [comp(nth1, [Ix2, L2, Xv]), comp('=', [R2, comp(c, [Xv1])])])]),
                                 comp('=', [R3, atom(none)])])],
                pp_teq(L1, L), pp_teq(L2, L), pp_teq(Len1, Len), pp_teq(Ix1, Ix), pp_teq(Ix2, Ix),
                pp_teq(Xv1, Xv), K1 =:= K, pp_teq(R2, R), pp_teq(R3, R) ),
              ( pp_fresh_vars(H, SrcVars, [Len, Ix, Xv], Fr),
                pp_needs_of(SrcVars, L, Nd),
                NR = nr([G], Nd, Fr, []) ),
              nd_fail(N, "template")).
node_rule(el_maplist, N, NR) :-
    N = nd(_, _, SrcVars, Sc, _, K, R, H, Goal, Subs, _),
    nd_producer(N, Ix, G),
    if_commit(( G = comp(maplist, [F0, L0, X]), nd_is_subj(N, X), is_var_t(F0, false) ),
              ( F = F0, L = L0 ), nd_fail(N, "producer")),
    pp_sub0(H, Subs, S0),
    if_commit(( Goal = comp(',', [SG, comp(';', [comp('->', [comp('=', [R0, comp(c, [Xv])]),
                                                             comp(',', [Call, comp('=', [R2, comp(c, [Yv])])])]),
                                                 comp('=', [R3, atom(none)])])]),
                pp_node_goal_is(S0, SG),
                add_args(F, [Xv, Yv], just(Call1)), pp_teq(Call1, Call),
                pp_teq(R2, R), pp_teq(R3, R) ),
              ( pp_fresh_vars(H, SrcVars, [R0, Xv, Yv], Fr),
                scope_before(Sc, Ix, Sc1),
                nd_recurse(N, Sc1, L, K, R0, S0, nr(C0, Nd0, F1, D0)),
                pp_needs_of(SrcVars, F, NdF),
                ord_union(Nd0, NdF, Nd),
                conc(Fr, F1, Fr1),
                NR = nr([G|C0], Nd, Fr1, D0) ),
              nd_fail(N, "template")).
node_rule(el_spec, N, NR) :-
    N = nd(Cx, _, SrcVars, Sc, Subject, K, R, H, Goal, _, _),
    Cx = ppcx(SrcProg, Specs, _),
    nd_producer(N, Ix, G),
    goal_key(G, MK),
    if_commit(MK = just(Key), true, nd_fail(N, "producer is not callable")),
    nd_need(N, prog_lookup(SrcProg, Key, just(_)), "producer is not a user predicate"),
    goal_args(G, GArgs),
    numbered_list(GArgs, 0, NGA),
    findall(I, ( member(I-A, NGA), pp_teq(A, Subject) ), Ps),
    if_commit(Ps = [Pos], true, nd_fail(N, "the subject is not exactly one argument of the producer")),
    subj_id(Subject, SId),
    nd_need(N, if_commit(( member(I-A, NGA), I =\= Pos, term_var_ids(A, AV), ord_memberchk(SId, AV) ), fail, true),
            "the subject also occurs in another argument"),
    Sp = spec(Key, Pos, K),
    pp_used_of(Cx, Sp, Used),
    ground_before(Sc, Ix, Gnd),
    nd_need(N, ord_memberchk(Sp, Specs), "the callee's program for this position is missing"),
    pp_sp_name(Sp, SpN),
    atom_concat(SpN, '__r', RN),
    if_commit(( Goal = comp(RN, Args1), same_length(Args1, GArgs) ), true, nd_fail(N, "template")),
    numbered_list(Args1, 0, NA1),
    maplist(pp_spec_arg(H, SrcVars, Pos, R, Used, Gnd), NGA, NA1, Frs),
    concat_lists(Frs, Fr),
    findall(Nb, ( member(I-B, NA1), I =\= Pos, pp_needs_of(SrcVars, B, Nb) ), Nbs),
    ord_union(Nbs, Nd),
    NR = nr([G], Nd, Fr, []).
node_rule(el_chain, N, NR) :-
    N = nd(Cx, _, SrcVars, Sc, _, K, R, H, Goal, Subs, _),
    nd_producer(N, Ix, G),
    concat_of(G, nd_is_subj(N), H, Mode, Parts),
    nd_need(N, same_length(Subs, Parts), "one closure per part"),
    scope_before(Sc, Ix, Sc1),
    maplist(check_closure(Cx, H, SrcVars, Sc1, Mode, K), Parts, Subs, Clos),
    pairs_keys_values(Clos, Cs, NRs),
    mk_list(Cs, atom('[]'), CL),
    nd_need(N, pp_teq(Goal, comp(plop2_chain, [int(K), CL, R])), "template"),
    nr_concat(NRs, nr(C0, Nd, Fr, D)),
    NR = nr([G|C0], Nd, Fr, D).
node_rule(el_chain_const, N, NR) :-
    N = nd(Cx, _, SrcVars, Sc, _, K, R, H, Goal, Subs, _),
    nd_producer(N, Ix, G),
    concat_of(G, nd_is_subj(N), H, Mode, Parts),
    nd_need(N, same_length(Subs, Parts), "one closure per part"),
    scope_before(Sc, Ix, Sc1),
    maplist(check_closure(Cx, H, SrcVars, Sc1, Mode, K), Parts, Subs, Clos),
    pairs_keys(Clos, Cs),
    closure_prefix_c(Cs, Prefix, _),
    length(Prefix, LP),
    nd_need(N, ( K =< LP, nth_det(K, Prefix, just(PK)), pp_teq(Goal, comp('=', [R, comp(c, [PK])])) ),
            "element is not in the static prefix"),
    findall(PG, member(comp(cl, [atom(cl_chain), _, _, comp(chain, [PG, _])]), Subs), ChainGoals),
    NR = nr([G|ChainGoals], [], [], []).
node_rule(el_branch, N, NR) :-
    branch_rule(N, NR).

subj_id(T, I) :-
    if_commit(T = var(I0, _), I = I0, I = -1).

none_ok(Sc, Subject, K) :-
    if_commit(Subject == atom('[]'), true,
    if_commit(Subject = atom(A), ( atom_length(A, L), L < K ),
    if_commit(Subject = int(X), ( number_codes(X, Cs), length(Cs, L), L < K ),
    if_commit(Subject = var(V, _),
              ( producer_in(Sc, V, nothing), Sc = scope(_, B, _), ord_nonmember(V, B) ),
              fail)))).

subject_text(T, Cs) :-
    if_commit(T = atom(A), atom_chars(A, Cs),
              ( T = int(X), number_codes(X, Codes), atom_codes(At, Codes), atom_chars(At, Cs) )).

codes_rule(Rule, N, NR) :-
    N = nd(_, _, SrcVars, Sc, _, K, R, H, Goal, Subs, _),
    nd_producer(N, Ix, G),
    if_commit(( Rule == el_codes_of_text, G = comp(atom_codes, [A, X]), nd_is_subj(N, X) ), T = A,
              if_commit(( Rule == el_text_of_codes, G = comp(atom_codes, [X, L]), nd_is_subj(N, X) ), T = L,
                        nd_fail(N, "producer"))),
    pp_sub0(H, Subs, S0),
    if_commit(( node_goal(S0, just(SG)),
                Goal = comp(',', [SG1, comp(';', [comp('->', [comp('=', [R0, comp(c, [TV])]),
                                                              comp(',', [comp(char_code, [Ch, Code]),
                                                                         comp('=', [R2, comp(c, [Res])])])]),
                                                  comp('=', [R3, atom(none)])])]),
                pp_teq(SG, SG1), pp_teq(R2, R), pp_teq(R3, R),
                codes_dir(Rule, TV, Res, Ch, Code) ),
              true, nd_fail(N, "template")),
    pp_fresh_vars(H, SrcVars, [R0, Ch, Code], Fr),
    scope_before(Sc, Ix, Sc1),
    nd_recurse(N, Sc1, T, K, R0, S0, nr(C0, Nd, F0, D)),
    conc(Fr, F0, F1),
    NR = nr([G|C0], Nd, F1, D).

codes_dir(el_codes_of_text, TV, Res, Ch, Code) :-
    pp_teq(TV, Ch),
    pp_teq(Res, Code).
codes_dir(el_text_of_codes, TV, Res, Ch, Code) :-
    pp_teq(TV, Code),
    pp_teq(Res, Ch).

pp_spec_arg(H, SrcVars, Pos, R, Used, Gnd, I-A, _-B, Fr) :-
    if_commit(I =:= Pos,
              ( pp_need(pp_teq(B, R), H, "result position"), Fr = [] ),
              if_commit(ord_memberchk(I, Used),
                        ( pp_need(pp_teq(A, B), H, "an argument the callee reads is not passed"),
                          pp_need(pp_gnd(A, Gnd), H, "an argument the callee reads is not ground at the call"),
                          Fr = [] ),
                        pp_fresh_vars(H, SrcVars, [B], Fr))).

%  concat_of(+Goal, +IsX, +H, -TextMode, -Parts)
concat_of(G, IsX, H, Mode, Parts) :-
    if_commit(( G = comp(append, [A, B, X]), call(IsX, X) ), ( Mode = false, Parts = [A, B] ),
    if_commit(( G = comp(F, [A, B, X]), memberchk(F, [atom_concat, string_concat]), call(IsX, X) ),
              ( Mode = true, Parts = [A, B] ),
    if_commit(( G = comp(atomic_list_concat, [L, X]), call(IsX, X) ),
              ( Mode = true, pp_list_of(L, Parts) ),
    if_commit(( G = comp(atomic_list_concat, [L, Sp, X]), call(IsX, X) ),
              ( Mode = true, pp_list_of(L, Ps), interleave_c(Sp, Ps, Parts) ),
              ( wmsg(H, "producer is not a concatenation", M), pp_fail(M) ))))).

interleave_c(S, Xs, Out) :-
    interleave_c0(Xs, S, Out).

interleave_c0([], _, []).
interleave_c0([X|Xs], S, Out) :-
    interleave_c_(Xs, S, X, Out).

interleave_c_([], _, X, [X]).
interleave_c_([Y|Ys], S, X, [X, S|Out]) :-
    interleave_c_(Ys, S, Y, Out).

%  closure_prefix_c(+Closures, -Prefix, -Complete)
closure_prefix_c([], [], true).
closure_prefix_c([C|Cs], P, Ok) :-
    if_commit(( C = comp(plop2_static, [L]), static_list(L, just(Xs)) ),
              ( closure_prefix_c(Cs, Rest, Ok), conc(Xs, Rest, P) ),
    if_commit(( C = comp(plop2_chain_c, [L]), static_list(L, just(Inner)) ),
              ( closure_prefix_c(Inner, Xs, Ok1),
                if_commit(Ok1 == true,
                          ( closure_prefix_c(Cs, Rest, Ok), conc(Xs, Rest, P) ),
                          ( P = Xs, Ok = false )) ),
              ( P = [], Ok = false ))).

is_var_id(W, X) :-
    X = var(I, _),
    I =:= W.

%  check_closure(+Cx, +H, +SrcVars, +Scope, +TextMode, +K, +Part, +Cl, -(Closure-NR))
check_closure(Cx, H, SrcVars, Sc, Mode, K, Part, Cl, Clo-NR) :-
    if_commit(Cl = comp(cl, [atom(Rule), P, Clo0, Info]), true,
              ( wmsg(H, "bad closure", M0), pp_fail(M0) )),
    pp_need(pp_teq(P, Part), H, "closure for another part"),
    Clo = Clo0,
    if_commit(closure_rule_known(Rule),
              closure_rule(Rule, cc(Cx, H, SrcVars, Sc, Mode, K, Part, Clo, Info), NR),
              ( wmsg(H, "unknown closure rule", M), pp_fail(M) )).

closure_rule_known(R) :-
    memberchk(R, [cl_static, cl_value, cl_spec, cl_chain]).

closure_rule(cl_static, cc(_, H, _, _, Mode, _, Part, Clo, _), NR) :-
    static_elems_c(Mode, Part, ME),
    if_commit(ME = just(Xs),
              ( mk_list(Xs, atom('[]'), XL),
                pp_need(pp_teq(Clo, comp(plop2_static, [XL])), H, "static part"),
                nr_empty(NR) ),
              ( wmsg(H, "part is not static", M), pp_fail(M) )).
closure_rule(cl_value, cc(_, H, SrcVars, _, _, _, Part, Clo, _), nr([], Nd, [], [])) :-
    pp_need(pp_teq(Clo, comp(plop2_value, [Part])), H, "value part"),
    pp_needs_of(SrcVars, Part, Nd).
closure_rule(cl_spec, cc(Cx, H, SrcVars, Sc, _, K, Part, Clo, Info), NR) :-
    Cx = ppcx(SrcProg, Specs, _),
    if_commit(Part = var(W, _), true, ( wmsg(H, "a spec part must be a variable", M1), pp_fail(M1) )),
    producer_in(Sc, W, MP),
    if_commit(( MP = just(Ix-PG), pp_teq(PG, Info) ), true,
              ( wmsg(H, "the recorded goal is not the part's first producer", M2), pp_fail(M2) )),
    goal_key(PG, MK),
    if_commit(MK = just(Key), true, ( wmsg(H, "producer not callable", M3), pp_fail(M3) )),
    pp_need(prog_lookup(SrcProg, Key, just(_)), H, "producer is not a user predicate"),
    goal_args(PG, PArgs),
    numbered_list(PArgs, 0, NPA),
    findall(I, ( member(I-A, NPA), pp_teq(A, Part) ), Qs),
    if_commit(Qs = [Pos], true, ( wmsg(H, "the part is not exactly one argument of its producer", M4), pp_fail(M4) )),
    findall(U, ( between(1, K, JJ), pp_used_of(Cx, spec(Key, Pos, JJ), U) ), Us),
    ord_union(Us, UsedAny),
    ground_before(Sc, Ix, Gnd),
    findall(I-A, ( member(I-A, NPA), I =\= Pos ), Others),
    forall_jj(1, K, H, Key, Pos, Specs),
    pp_d_name(Key, Pos, K, DN),
    if_commit(( Clo = comp(DN, CArgs), same_length(CArgs, Others) ), true,
              ( wmsg(H, "dispatcher closure", M5), pp_fail(M5) )),
    maplist(closure_arg(H, SrcVars, UsedAny, Gnd), Others, CArgs, Frs),
    concat_lists(Frs, Fr),
    maplist(term_var_ids, CArgs, CVs),
    ord_union(CVs, CV),
    ord_intersection(CV, SrcVars, Nd),
    NR = nr([PG], Nd, Fr, [t(Key, Pos, K)]).
closure_rule(cl_chain, cc(Cx, H, SrcVars, Sc, _, K, Part, Clo, Info), NR) :-
    if_commit(Part = var(W, _), true, ( wmsg(H, "a chain part must be a variable", M1), pp_fail(M1) )),
    if_commit(Info = comp(chain, [PG, L]), pp_list_of(L, SubCls), ( wmsg(H, "chain info", M2), pp_fail(M2) )),
    producer_in(Sc, W, MP),
    if_commit(( MP = just(Ix-G), pp_teq(G, PG) ), true,
              ( wmsg(H, "the recorded goal is not the part's first producer", M3), pp_fail(M3) )),
    concat_of(PG, is_var_id(W), H, InnerText, InnerParts),
    pp_need(same_length(SubCls, InnerParts), H, "one closure per inner part"),
    scope_before(Sc, Ix, Sc1),
    maplist(check_closure(Cx, H, SrcVars, Sc1, InnerText, K), InnerParts, SubCls, Inner),
    pairs_keys_values(Inner, Cs, NRs),
    mk_list(Cs, atom('[]'), CL),
    pp_need(pp_teq(Clo, comp(plop2_chain_c, [CL])), H, "nested chain"),
    nr_concat(NRs, nr(C0, Nd, Fr, D)),
    NR = nr([PG|C0], Nd, Fr, D).

forall_jj(J, K, H, Key, Pos, Specs) :-
    if_commit(J > K, true,
              ( format(string(M), "~wmissing program for position ~d", [H, J]),
                pp_ensure(ord_memberchk(spec(Key, Pos, J), Specs), M),
                J1 is J + 1,
                forall_jj(J1, K, H, Key, Pos, Specs) )).

closure_arg(H, SrcVars, UsedAny, Gnd, I-A, B, Fr) :-
    if_commit(ord_memberchk(I, UsedAny),
              ( pp_need(pp_teq(A, B), H, "an argument the callee reads is not passed"),
                pp_need(pp_gnd(A, Gnd), H, "an argument the callee reads is not ground at the call"),
                Fr = [] ),
              ( pp_need(is_fresh_in(SrcVars, B), H, "an unused argument is not a fresh variable"),
                findall(X, B = var(X, _), Fr) )).

static_elems_c(Mode, Part, M) :-
    if_commit(( Mode == true, Part = atom(A) ),
              ( atom_chars(A, Cs), maplist(wrap_atom, Cs, Xs), M = just(Xs) ),
    if_commit(( Mode == true, Part = int(X) ),
              ( number_codes(X, Codes), atom_codes(At, Codes), atom_chars(At, Cs),
                maplist(wrap_atom, Cs, Xs), M = just(Xs) ),
              ground_list_c(Part, M))).

wrap_atom(C, atom(C)).

ground_list_c(T, M) :-
    if_commit(T == atom('[]'), M = just([]),
              if_commit(( T = comp('.', [X, Tl]), term_var_ids(X, []) ),
                        ( ground_list_c(Tl, M0), maybe_cons(M0, X, M) ),
                        M = nothing)).

% ---------------------------------------------------------------------------
% Branches

branch_rule(N, NR) :-
    N = nd(Cx, Here, SrcVars, Sc, Subject, K, R, H, Goal, Subs, Info),
    Cx = ppcx(SrcProg, _, _),
    nd_producer(N, Ix, G),
    if_commit(G = comp(';', [comp('->', [C0, T0]), E0]), ( MC = just(C0), T = T0, E = E0 ),
    if_commit(G = comp('->', [C0, T0]), ( MC = just(C0), T = T0, E = atom(fail) ),
    if_commit(G = comp(if_commit, [C0, T0, E0]), ( MC = just(C0), T = T0, E = E0 ),
    if_commit(G = comp(';', [A0, B0]), ( MC = nothing, T = A0, E = B0 ),
              nd_fail(N, "producer is not a branch"))))),
    if_commit(Info = comp(branch, [_, IA, IB, IC]),
              ( slice_of(IA, KC, DC, CC), slice_of(IB, KT, DT, CT), slice_of(IC, KE, DE, CE) ),
              nd_fail(N, "branch slices")),
    if_commit(Subs = [NT, NE], true, nd_fail(N, "two branch derivations")),
    if_commit(MC = just(CG), conj_list(CG, Cs), Cs = []),
    conj_list(T, Ts),
    conj_list(E, Es),
    Sc = scope(Gs, Bound, Ground),
    Ix1 is Ix - 1,
    take(Ix1, Gs, BeforeGs),
    maplist(term_var_ids, BeforeGs, BVs),
    ord_union([Bound|BVs], BoundB),
    ground_before(Sc, Ix, GroundB),
    maplist(term_var_ids, Cs, CVs),
    ord_union([BoundB|CVs], BoundT),
    foldl(pp_g_after_f, Cs, GroundB, GroundT),
    ScC = scope(Cs, BoundB, GroundB),
    ScT = scope(Ts, BoundT, GroundT),
    ScE = scope(Es, BoundB, GroundB),
    branch_part(H, SrcProg, KC, DC, CC, Cs, ScC),
    branch_part(H, SrcProg, KT, DT, CT, Ts, ScT),
    branch_part(H, SrcProg, KE, DE, CE, Es, ScE),
    if_commit(node_goal(NT, just(GT)), true, nd_fail(N, "then derivation")),
    if_commit(node_goal(NE, just(GE)), true, nd_fail(N, "else derivation")),
    pick_kept(KT, Ts, PT),
    pick_kept(KE, Es, PE),
    pick_kept(KC, Cs, PC),
    conc(PT, [GT], TGs), mk_conj(TGs, ThenG),
    conc(PE, [GE], EGs), mk_conj(EGs, ElseG),
    mk_conj(PC, CondG),
    if_commit(MC == nothing, Expected = comp(';', [ThenG, ElseG]),
              if_commit(G = comp(if_commit, _),
                        Expected = comp(if_commit, [CondG, ThenG, ElseG]),
                        Expected = comp(';', [comp('->', [CondG, ThenG]), ElseG]))),
    nd_need(N, pp_teq(Goal, Expected), "template"),
    concat_lists([BeforeGs, Cs, Ts], GsT),
    conc(BeforeGs, Es, GsE),
    check_node(Cx, Here, SrcVars, scope(GsT, Bound, Ground), Subject, K, R, NT, nr(ConsT, NeedsT, FreshT, DispT)),
    check_node(Cx, Here, SrcVars, scope(GsE, Bound, Ground), Subject, K, R, NE, nr(ConsE, NeedsE, FreshE, DispE)),
    concat_lists([Cs, Ts, Es], Local),
    pick_kept(CC, Cs, ClC), pick_kept(CT, Ts, ClT), pick_kept(CE, Es, ClE),
    concat_lists([ClC, ClT, ClE], Claimed),
    conc(ConsT, ConsE, ConsTE),
    findall(X, ( member(X, ConsTE), term_member_c(X, Local) ), FromNodes),
    nd_need(N, same_shown(Claimed, FromNodes), "branch consumption"),
    vars_of_list(PT, VPT), ord_intersection(VPT, SrcVars, RT0), ord_union(RT0, NeedsT, ReadT),
    vars_of_list(PE, VPE), ord_intersection(VPE, SrcVars, RE0), ord_union(RE0, NeedsE, ReadE),
    vars_of_list(PC, VPC), ord_intersection(VPC, SrcVars, ReadC),
    vars_of_list(Cs, VC), ord_subtract(VC, BoundB, ProdC),
    vars_of_list(Ts, VT), ord_subtract(VT, BoundT, ProdT),
    vars_of_list(Es, VE), ord_subtract(VE, BoundB, ProdE),
    kept_prod(KT, ScT, KPT), kept_prod(KC, ScC, KPC), kept_prod(KE, ScE, KPE),
    ord_subtract(ProdT, KPT, DT1), ord_subtract(ProdC, KPC, DC1), ord_subtract(ProdE, KPE, DE1),
    nd_need(N, ord_intersection(ReadT, DT1, []), "then-branch reads a dropped goal's variable"),
    nd_need(N, ord_intersection(ReadT, DC1, []), "then-branch reads a dropped condition variable"),
    nd_need(N, ord_intersection(ReadE, DE1, []), "else-branch reads a dropped goal's variable"),
    ord_union(ProdT, ProdC, PTC),
    ord_subtract(ReadT, PTC, O1),
    ord_subtract(ReadE, ProdE, O2),
    ord_subtract(ReadC, ProdC, O3),
    ord_union([O1, O2, O3], Outer),
    findall(X, ( member(X, ConsTE), not_term_member_c(X, Local) ), Outside),
    conc(FreshT, FreshE, Fresh),
    conc(DispT, DispE, Disp),
    NR = nr([G|Outside], Outer, Fresh, Disp).

branch_part(H, SrcProg, Kp, Dr, Co, Xs, Scx) :-
    length(Xs, L),
    check_partition(H, L, Kp, Dr, Co),
    check_certs(H, SrcProg, Scx, Dr).

kept_prod(Kept, scope(Gs, B, _), P) :-
    with_produced(B, Gs, Prods),
    numbered_list(Prods, 1, NP),
    findall(Pr, ( member(I-(_-Pr), NP), memberchk(I, Kept) ), Ps),
    ord_union(Ps, P).

vars_of_list(Ts, Vs) :-
    maplist(term_var_ids, Ts, VL),
    ord_union(VL, Vs).

term_member_c(X, L) :-
    if_commit(( member(Y, L), pp_teq(X, Y) ), true, fail).

not_term_member_c(X, L) :-
    if_commit(term_member_c(X, L), fail, true).

% ---------------------------------------------------------------------------
% Formula clauses: exact on the domain by exhaustive evaluation

check_formula(Gen, S, Cl) :-
    if_commit(S = comp(formula_step, [St, int(Lo), int(Hi), int(D), ClT]), true, pp_fail("bad formula_step")),
    pp_sp_of(St, Sp),
    Sp = spec(_/N, J, _),
    pp_as_clause(ClT, Cl),
    with_prelude(Gen, Prog),
    pp_sp_name(Sp, Name),
    Cl = clause(H, _, _),
    goal_key(H, MK),
    pp_ensure(MK == just(Name/N), "formula_step: wrong head"),
    atom_concat(Name, '__r', RN),
    forall_formula(Lo, Hi, Prog, Name, RN, N, J, D).

forall_formula(X, Hi, Prog, Name, RN, N, J, D) :-
    if_commit(X > Hi, true,
              ( formula_args(N, J, D, X, var(0, 'C'), AF),
                formula_args(N, J, D, X, var(0, 'R'), AR),
                first_of(Prog, comp(Name, AF), var(0, 'C'), VF),
                first_of(Prog, comp(RN, AR), var(0, 'R'), VS),
                format(string(M), "formula_step for ~w: the formula and the sliced program differ at ~d", [Name, X]),
                pp_ensure(formula_agree(VF, VS), M),
                X1 is X + 1,
                forall_formula(X1, Hi, Prog, Name, RN, N, J, D) )).

formula_args(N, J, D, X, V, As) :-
    N1 is N - 1,
    findall(A, ( between(0, N1, I), formula_arg(I, J, D, X, V, A) ), As).

formula_arg(I, J, D, X, V, A) :-
    if_commit(I =:= J, A = V,
              if_commit(I =:= D, A = int(X),
                        ( I10 is I + 10, A = var(I10, '_') ))).

formula_agree(VF, VS) :-
    if_commit(( VF = right(just(A)), VS = right(just(comp(c, [B]))) ), pp_teq(A, B),
              ( VF = right(nothing), VS = right(just(atom(none))) )).

first_of(Prog, G, V, E) :-
    default_options(Opts),
    run_goal(Opts, Prog, G, 100, S),
    head_answer(S, _, R),
    first_result(R, V, E).

first_result(first(St), V, right(just(T))) :-
    resolve(V, St, T).
first_result(stop(M), _, left(M)).
first_result(none, _, right(nothing)).

% ---------------------------------------------------------------------------
% Input-character facts: symbolic evaluation on character variables

check_input_chars(Gen, S, Cl) :-
    if_commit(S = comp(input_chars_step, [St, ClT]), true, pp_fail("bad input_chars_step")),
    pp_sp_of(St, Sp),
    Sp = spec(_/N, J, _),
    pp_as_clause(ClT, Cl),
    pp_sp_name(Sp, Name),
    Cl = clause(H, Body, _),
    goal_args(H, HArgs),
    with_prelude(Gen, Prog),
    atom_concat(Name, '__in', InN),
    goal_key(H, MK),
    pp_ensure(MK == just(InN/N), "input_chars_step: wrong head"),
    atom_concat(Name, '__r', RN),
    J1 is J + 1,
    nth_det(J1, HArgs, just(CJ)),
    if_commit(Body == atom(true),
              symbolic_chars(Prog, Name, RN, HArgs, J, CJ),
              ( replace_nth0(HArgs, J, comp(c, [CJ]), WArgs),
                format(string(M), "input_chars_step for ~w: wrapper", [Name]),
                pp_ensure(pp_teq(Body, comp(RN, WArgs)), M) )).

symbolic_chars(Prog, Name, RN, HArgs, J, CJ) :-
    numbered_list(HArgs, 0, NHA),
    findall(V, ( member(I-A, NHA), I =\= J, term_var_ids(A, V) ), VL),
    ord_union(VL, InputVars),
    RV = var(999999, 'R'),
    replace_nth0(HArgs, J, RV, GArgs),
    run_goal(opts(100000, false, InputVars), Prog, comp(RN, GArgs), 1000000, Str),
    take_events(3, Str, Evs),
    findall(St1, member(ans(St1), Evs), Ans),
    findall(E, member(err(E), Evs), Errs),
    format(string(M0), "input_chars_step for ~w: the symbolic run does not give exactly one answer", [Name]),
    pp_ensure(( Ans = [_], Errs = [] ), M0),
    Ans = [St1],
    findall(W, ( member(V, InputVars), walk(var(V, ''), St1, W) ), Ws),
    findall(I, member(var(I, _), Ws), WIds),
    format(string(M1), "input_chars_step for ~w: the run constrains the input characters", [Name]),
    pp_ensure(( same_length(WIds, Ws), sort(WIds, SW), same_length(SW, Ws) ), M1),
    resolve(RV, St1, RR),
    rename_back(InputVars, St1, RR, RR1),
    format(string(M2), "input_chars_step for ~w: the symbolic run gives another character", [Name]),
    pp_ensure(pp_teq(RR1, comp(c, [CJ])), M2).

rename_back(InputVars, St, T, T1) :-
    if_commit(T = var(W, _),
              if_commit(( member(V, InputVars), walk(var(V, ''), St, var(W1, _)), W1 =:= W ),
                        T1 = var(V, ''), T1 = T),
              if_commit(T = comp(F, As),
                        ( maplist(rename_back(InputVars, St), As, Bs), T1 = comp(F, Bs) ),
                        T1 = T)).

take_events(N, S, Evs) :-
    if_commit(N =< 0, Evs = [],
              ( force(S, F),
                if_commit(F = [E|T],
                          ( N1 is N - 1, take_events(N1, T, Evs1), Evs = [E|Evs1] ),
                          Evs = []) )).
