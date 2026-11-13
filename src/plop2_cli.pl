/*  plop2_cli.pl - the plop2 commands (port of the Haskell app/Main.hs).

    Commands write to the current output and to user_error.  die/1 writes
    "plop2: Message" to user_error and throws cli_exit(1).
*/

usage_text(T) :-
    atomic_list_concat([
      "plop2 - one separate, minimal, proved program per output character",
      "",
      "  plop2 chars FILE NAME/ARITY N [--out-arg I] [-o OUT]",
      "        write NAME__char1 .. NAME__charN, each computing only its character",
      "  plop2 run FILE GOAL N [--out-arg I] [-o OUT]",
      "        give the inputs as character lists (\"...\"); each position's program is run",
      "        on input character variables I1..Im, then on the input; compares with the",
      "        original algorithm's output",
      "  plop2 formula FILE NAME/ARITY N --domain LO..HI [--domain-arg I] [--mnns DIR] [-o OUT]",
      "        closed forms per position for an integer input, found with mnns AlgebraPLOp",
      "  plop2 proof-check FILE OUT OUT.proof",
      "        check a proof independently",
      "",
      "Argument positions are 1-based; the output argument defaults to the last.",
      "Every output is proof-gated: it is written only if Plop2.Proof accepts its proof.",
      ""], '\n', T).

die(Msg) :-
    format(user_error, "plop2: ~w~n", [Msg]),
    throw(cli_exit(1)).

% ---------------------------------------------------------------------------
% Flags: pf(OutArg, OutFile, Domain, DomainArg, Mnns, PositionalRev)

parse_flags(Args, E) :-
    catch(( flags_go(Args, pf(nothing, nothing, nothing, 1, nothing, []), F), E = right(F) ),
          flag_error(M), E = left(M)).

flags_go([], pf(OA, OF, D, DA, Mn, P), pf(OA, OF, D, DA, Mn, P1)) :-
    rev(P, P1).
flags_go([A|As], F0, F) :-
    atom_string(A, AS),
    flag_kind(AS, As, K),
    flag_step(K, AS, As, F0, F).

flag_kind(AS, As, K) :-
    if_commit(( AS == "--out-arg", As = [_|_] ), K = outarg,
    if_commit(( AS == "-o", As = [_|_] ), K = out,
    if_commit(( AS == "--domain", As = [_|_] ), K = domain,
    if_commit(( AS == "--domain-arg", As = [_|_] ), K = domainarg,
    if_commit(( AS == "--mnns", As = [_|_] ), K = mnns,
    if_commit(string_concat("--", _, AS), K = unknown,
              K = positional)))))).

flag_step(outarg, _, [I|R], pf(_, OF, D, DA, Mn, P), F) :-
    read_int(I, N),
    flags_go(R, pf(just(N), OF, D, DA, Mn, P), F).
flag_step(out, _, [O|R], pf(OA, _, D, DA, Mn, P), F) :-
    atom_string(O, OS),
    flags_go(R, pf(OA, just(OS), D, DA, Mn, P), F).
flag_step(domain, _, [X|R], pf(OA, OF, _, DA, Mn, P), F) :-
    atom_string(X, XS),
    if_commit(( sub_string(XS, B, 2, _, ".."), split_domain(XS, B, Lo, Hi) ),
              flags_go(R, pf(OA, OF, just(Lo-Hi), DA, Mn, P), F),
              throw(flag_error("--domain expects LO..HI"))).
flag_step(domainarg, _, [I|R], pf(OA, OF, D, _, Mn, P), F) :-
    read_int(I, N),
    flags_go(R, pf(OA, OF, D, N, Mn, P), F).
flag_step(mnns, _, [X|R], pf(OA, OF, D, DA, _, P), F) :-
    atom_string(X, XS),
    flags_go(R, pf(OA, OF, D, DA, just(XS), P), F).
flag_step(unknown, AS, _, _, _) :-
    string_concat("unknown option ", AS, M),
    throw(flag_error(M)).
flag_step(positional, AS, R, pf(OA, OF, D, DA, Mn, P), F) :-
    flags_go(R, pf(OA, OF, D, DA, Mn, [AS|P]), F).

%  Haskell's break (== '.'): the split is at the first '.', which must
%  start "..".
split_domain(XS, B, Lo, Hi) :-
    once_det(sub_string(XS, 0, B, _, LoS)),
    if_commit(sub_string(LoS, _, _, _, "."), fail, true),
    B2 is B + 2,
    once_det(sub_string(XS, B2, _, 0, HiS)),
    read_int(LoS, Lo),
    read_int(HiS, Hi).

read_int(X, N) :-
    if_commit(catch(number_string(N0, X), _, fail), N = N0, throw(flag_error("Prelude.read: no parse"))).

fl_out_arg(pf(OA, _, _, _, _, _), OA).
fl_out_file(pf(_, OF, _, _, _, _), OF).
fl_domain(pf(_, _, D, _, _, _), D).
fl_domain_arg(pf(_, _, _, DA, _, _), DA).
fl_mnns(pf(_, _, _, _, Mn, _), Mn).
fl_pos(pf(_, _, _, _, _, P), P).

% ---------------------------------------------------------------------------

cli([]) :-
    usage_text(T),
    write(T).
cli([Cmd|Rest]) :-
    if_commit(Cmd == help,
              ( usage_text(T), write(T) ),
              ( parse_flags(Rest, E),
                cli_flags(E, Cmd) )).

cli_flags(left(M), _) :-
    die(M).
cli_flags(right(Fl), Cmd) :-
    fl_pos(Fl, Pos),
    atom_string(Cmd, CS),
    if_commit(dispatch_known(CS, Pos), dispatch(CS, Pos, Fl), bad_arguments).

bad_arguments :-
    usage_text(U),
    string_concat("bad arguments\n", U, M),
    die(M).

dispatch_known("chars", [_, _, _]).
dispatch_known("run", [_, _, _]).
dispatch_known("formula", [_, _, _]).
dispatch_known("proof-check", [_, _, _]).

dispatch("chars", [File, KeyS, NS], Fl) :-
    load_cut_free(File, P, Evs),
    parse_key(KeyS, Key),
    read_int_or_die(NS, N),
    out_pos(Fl, Key, J),
    slice_positions(P, Key, J, N, SR),
    generated(P, SR, Key, J, N, [], Prog),
    sr_steps(SR, Steps),
    proved(P, Steps, Prog, Report),
    conc(Evs, Report, HL),
    header(File, HL, SR, Hdr),
    write_out(Fl, Hdr, Prog, Steps).
dispatch("run", [File, GoalS, NS], Fl) :-
    read_int_or_die(NS, N),
    run_cmd(Fl, File, GoalS, N).
dispatch("formula", [File, KeyS, NS], Fl) :-
    read_int_or_die(NS, N),
    formula_cmd(Fl, File, KeyS, N).
dispatch("proof-check", [File, Out, ProofFile], _) :-
    load_cut_free(File, P, _),
    read_text(Out, OT),
    parse_program(OT, PE),
    or_die_prefixed(PE, Out, Prog),
    read_text(ProofFile, PT),
    read_proof(PT, SE),
    or_die_prefixed(SE, ProofFile, Steps),
    check_plop_proof(P, Steps, Prog, CE),
    if_commit(CE = right(Lines),
              forall_lines(Lines),
              ( CE = left(M), string_concat("proof rejected: ", M, DM), die(DM) )).

forall_lines([]).
forall_lines([L|Ls]) :-
    format("~w~n", [L]),
    forall_lines(Ls).

or_die_prefixed(E, Path, X) :-
    if_commit(E = right(X0), X = X0,
              ( E = left(M), format(string(DM), "~w: ~w", [Path, M]), die(DM) )).

read_int_or_die(S, N) :-
    if_commit(catch(number_string(N0, S), _, fail), N = N0, die("Prelude.read: no parse")).

out_pos(Fl, _/A, J) :-
    fl_out_arg(Fl, OA),
    if_commit(OA = just(I), J is I - 1, J is A - 1).

read_text(Path, Text) :-
    catch(read_file_to_string(Path, Text, [encoding(utf8)]), _,
          ( format(string(M), "~w: openFile: does not exist (No such file or directory)", [Path]), die(M) )).

load_cut_free(Path, P, Evs) :-
    read_text(Path, Src),
    parse_program(Src, PE),
    or_die_prefixed(PE, Path, P0),
    eliminate_cuts(P0, E),
    if_commit(E = right(P-Es),
              maplist(show_cut_event, Es, Evs),
              ( E = left(Bad), maplist(show_cut_event, Bad, BS),
                atomic_list_concat(BS, '\n  ', BA),
                format(string(M), "cuts that cannot be converted:\n  ~w", [BA]),
                die(M) )).

parse_key(S, F/N) :-
    if_commit(( once_det(sub_string(S, B, 1, _, "/")), B > 0 ),
              ( once_det(sub_string(S, 0, B, _, FS)),
                B1 is B + 1,
                once_det(sub_string(S, B1, _, 0, NS)),
                atom_string(F, FS),
                read_int_or_die(NS, N) ),
              ( string_concat("expected NAME/ARITY, got ", S, M), die(M) )).

sr_clauses(sres(C, _, _, _, _), C).
sr_used(sres(_, U, _, _, _), U).
sr_disp(sres(_, _, D, _, _), D).
sr_steps(sres(_, _, _, S, _), S).
sr_notes(sres(_, _, _, _, N), N).

%  Check the proof; nothing unproved is written or run.
proved(P, Steps, Prog, Report) :-
    check_plop_proof(P, Steps, Prog, E),
    if_commit(E = right(R), Report = R,
              ( E = left(M), string_concat("proof rejected: ", M, DM), die(DM) )).

header(File, Evs, SR, Text) :-
    sr_notes(SR, Notes),
    sort(Notes, SNotes),
    findall(L, ( member(E, Evs), format(string(L), "% ~w", [E]) ), EL),
    findall(L, ( member(X, SNotes), format(string(L), "% note: ~w", [X]) ), NL),
    format(string(L1), "% plop2: one program per output character, generated from ~w", [File]),
    concat_lists([[L1,
                   "% NAME__charK(In..., C) computes only character K.  Each clause keeps only the",
                   "% goals that bind what character K needs (or that may fail); every dropped goal",
                   "% has a totality certificate, and the proof is in the .proof file.",
                   "% The code is cut-free (runs on detlog2 and SWI-Prolog)."], EL, NL], Ls),
    unlines(Ls, Text).

unlines(Ls, Text) :-
    findall(X, ( member(L, Ls), member(X, [L, "\n"]) ), Parts),
    atomic_list_concat(Parts, A),
    atom_string(A, Text).

%  The per-position programs (wrappers, then __alt clauses), dispatchers,
%  helpers and the source predicates that kept goals still call.
generated(P, SR, Key, J, N, Extra, Prog) :-
    findall(spec(Key, J, K), between(1, N, K), Roots),
    sr_clauses(SR, ClMap),
    map_keys(ClMap, Keys),
    findall(Sp, ( member(Sp, Keys), not_memberchk(Sp, Roots) ), Others0),
    msort(Others0, Others),
    conc(Roots, Others, Ordered),
    findall(K1, ( member(clause(H, _, _), Extra), goal_key(H, just(K1)) ), Rep0),
    sort(Rep0, Replaced),
    findall(C, ( member(Sp, Ordered), spec_clause(ClMap, Replaced, Sp, C) ), SpecCls),
    sr_disp(SR, Disp),
    findall(C, ( member(t(K2, O, KK), Disp), dispatcher_clause(K2, O, KK, C) ), DispCls),
    concat_lists([Extra, SpecCls, DispCls], Roots1),
    reachable_source(P, Roots1, Used),
    helper_source(HS),
    parse_program(HS, HE),
    if_commit(HE = right(HP), true, ( HE = left(HM), string_concat("helpers: ", HM, HMM), throw(error(HMM)) )),
    program_clauses(HP, HKCs),
    findall(C, ( member(_-Cs, HKCs), member(C, Cs) ), HelperCls),
    program_clauses(P, PKCs),
    findall(C, ( member(K3-Cs, PKCs), ord_memberchk(K3, Used), member(C, Cs) ), SrcCls),
    concat_lists([Extra, SpecCls, DispCls, HelperCls, SrcCls], Cls),
    program_from_clauses(Cls, Prog).

spec_clause(ClMap, Replaced, Sp, C) :-
    Sp = spec(K, O, KK),
    wrapper_clauses(K, O, KK, Ws),
    map_find(ClMap, Sp, [], Alts),
    findall(W, ( member(W, Ws), W = clause(WH, _, _), goal_key(WH, just(WK)), ord_nonmember(WK, Replaced) ), Ws1),
    conc(Ws1, Alts, All),
    member(C, All).

:- relation(spec_clause/4).

reachable_source(P, Cls, Used) :-
    findall(K, ( member(clause(_, B, _), Cls), calls_of(B, Ks), member(K, Ks) ), Ks0),
    reach_go(Ks0, P, [], Used).

reach_go([], _, Seen, Seen).
reach_go([K|Ks], P, Seen, Used) :-
    if_commit(( ord_nonmember(K, Seen), prog_lookup(P, K, just(Cs)) ),
              ( ord_add_element(Seen, K, Seen1),
                findall(K1, ( member(clause(_, B, _), Cs), calls_of(B, Ks1), member(K1, Ks1) ), New),
                conc(Ks, New, Ks2),
                reach_go(Ks2, P, Seen1, Used) ),
              reach_go(Ks, P, Seen, Used)).

calls_of(T, Ks) :-
    if_commit(( T = comp(Op, As), memberchk(Op, [',', ';', '->', if_commit, '\\+', findall, forall, once]) ),
              ( maplist(calls_of, As, KL), concat_lists(KL, Ks) ),
              ( goal_key(T, M), if_commit(M = just(K), Ks = [K], Ks = []) )).

write_out(Fl, Hdr, Prog, Steps) :-
    show_program(Prog, PS),
    atomic_list_concat([Hdr, "\n", PS], A),
    fl_out_file(Fl, OF),
    if_commit(OF = just(O),
              ( write_file(O, A),
                string_concat(O, ".proof", PO),
                proof_text(Steps, PT),
                write_file(PO, PT),
                format(user_error, "wrote ~w and ~w~n", [O, PO]) ),
              write(A)).

write_file(Path, Text) :-
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]), write(S, Text), close(S)).

%  first_value(+Prog, +Goal, +NVars, +T, -Either)
first_value(Prog, G, NV, T, E) :-
    default_options(Opts),
    run_goal(Opts, Prog, G, NV, S),
    head_answer(S, _, R),
    first_result(R, T, E).

% ---------------------------------------------------------------------------
% run: input character variables

run_cmd(Fl, File, GoalS, N) :-
    load_cut_free(File, P, Evs),
    parse_query(GoalS, QE),
    if_commit(QE = right(Goal-_-NV), true,
              ( QE = left(QM), string_concat("goal: ", QM, DM), die(DM) )),
    goal_key(Goal, MK),
    if_commit(MK = just(Key), true, die("goal is not callable")),
    goal_args(Goal, Args),
    length(Args, LA),
    fl_out_arg(Fl, OA),
    if_commit(OA = just(OI), J is OI - 1, J is LA - 1),
    numbered_list(Args, 0, NArgs),
    findall(I-A, ( member(I-A, NArgs), I =\= J ), Inputs),
    maplist(input_given, Inputs),
    findall(I-Cs, ( member(I-A, Inputs), chars_of(A, just(Cs)) ), TextInputs),
    slice_positions(P, Key, J, N, SR),
    generated(P, SR, Key, J, N, [], Base),
    with_prelude(Base, Prog),
    maplist(sym_arg(J, TextInputs), NArgs, SymArgs),
    findall(V, ( member(A, SymArgs), term_vars_ordered(A, Vs), member(var(V, _), Vs) ), IV0),
    sort(IV0, InputVarIds),
    sr_steps(SR, SSteps),
    proved(P, SSteps, Base, _),
    read_text(File, Src0Text),
    parse_program(Src0Text, S0E),
    if_commit(S0E = right(Src0), true, ( S0E = left(S0M), die(S0M) )),
    with_prelude(Src0, RP),
    default_options(Opts),
    ref_run(Opts, RP, Goal, NV, RefS),
    head_answer(RefS, _, RefR),
    J1 is J + 1,
    nth_det(J1, Args, just(OutT)),
    if_commit(RefR = first(RSt), ( resolve(OutT, RSt, OutV), elements_of(OutV, RefElems) ), RefElems = nothing),
    findall(K, between(1, N, K), Ks),
    maplist(run_position(Prog, Key, J, Args, SymArgs, InputVarIds, TextInputs), Ks, Results),
    findall(C, member(r(_, _, C, _), Results), Extra),
    findall(comp(input_chars_step, [ST, comp(':-', [H, B])]),
            ( member(r(K, _, clause(H, B, _), _), Results), spec_term(spec(Key, J, K), ST) ), InSteps),
    findall(V, member(r(_, V, _, _), Results), Produced),
    take_while_just(Produced, Prefix),
    generated(P, SR, Key, J, N, Extra, ProgOut),
    conc(SSteps, InSteps, Steps),
    proved(P, Steps, ProgOut, Report),
    format("goal: ~w~n", [GoalS]),
    maplist(print_result, Results),
    maplist(show_char_c, Prefix, PCs),
    atomic_list_concat(PCs, PA),
    plop2_show_string(PA, PSh),
    format("characters 1..~d: ~w~n", [N, PSh]),
    forall_report(Report),
    compare_ref(RefElems, N, Prefix, Produced, Ok),
    fl_out_file(Fl, OF),
    if_commit(OF = just(_),
              ( conc(Evs, Report, HL),
                header(File, HL, SR, Hdr0),
                string_concat(Hdr0, "% NAME__charK__in: the program for character K over input character variables.\n", Hdr),
                write_out(Fl, Hdr, ProgOut, Steps) ),
              true),
    if_commit(Ok == true, true, throw(cli_exit(1))).

forall_report([]).
forall_report([L|Ls]) :-
    format("  ~w~n", [L]),
    forall_report(Ls).

input_given(I-A) :-
    term_vars_ordered(A, Vs),
    if_commit(Vs == [], true,
              ( I1 is I + 1,
                format(string(M), "input argument ~d must be given (as a character list \"...\")", [I1]),
                die(M) )).

sym_arg(J, TextInputs, I-A, S) :-
    if_commit(I =:= J, S = atom('$out'),
              if_commit(memberchk(I-Cs, TextInputs),
                        ( length(TextInputs, NT), length(Cs, L),
                          findall(var(Id, Nm), ( between(1, L, Q), Id is 1000 * (I + 1) + Q, input_name(NT, I, Q, Nm) ), Vs),
                          mk_list(Vs, atom('[]'), S) ),
                        S = A)).

input_name(NT, I, Q, Nm) :-
    if_commit(NT =:= 1,
              format(atom(Nm), "I~d", [Q]),
              ( I1 is I + 1, format(atom(Nm), "I~d_~d", [I1, Q]) )).

take_while_just([], []).
take_while_just([M|Ms], P) :-
    if_commit(M = just(X), ( take_while_just(Ms, P0), P = [X|P0] ), P = []).

print_result(r(K, V, _, How)) :-
    if_commit(V = just(T), show_term_q(T, S), S = "-"),
    format("  char ~d: ~w   (~w)~n", [K, S, How]).

compare_ref(nothing, _, _, _, true) :-
    format("original algorithm: no output (it failed or raised an error)~n").
compare_ref(just(Es), N, Prefix, Produced, Ok) :-
    take(N, Es, Want),
    maplist(show_char_c, Want, WCs),
    atomic_list_concat(WCs, WA),
    plop2_show_string(WA, WSh),
    format("original algorithm, first ~d: ~w~n", [N, WSh]),
    length(Want, LW),
    test(( length(Prefix, LW), want_agrees(Want, Produced), drop(LW, Produced, Rest),
           all_nothing(Rest) ), Ok),
    if_commit(Ok == true,
              format("match: every position agrees with the original output~n"),
              format("MISMATCH with the original output~n")).

want_agrees([], _).
want_agrees([W|Ws], Ps) :-
    if_commit(Ps = [just(X)|Ps1], ( pp_teq(X, W), want_agrees(Ws, Ps1) ), Ps == []).

all_nothing([]).
all_nothing([nothing|Ms]) :-
    all_nothing(Ms).

%  One position: a fact over the input character variables, a "none" fact,
%  or the wrapper over the sliced program (with the value on the input).
run_position(Prog, Key, J, Args, SymArgs, InputVarIds, TextInputs, K, r(K, Value, Clause, How)) :-
    Sp = spec(Key, J, K),
    spec_name(Sp, Name),
    r_name(Sp, RN),
    RVar = var(900000, 'R'),
    CVar = var(900001, 'C'),
    replace_nth0(SymArgs, J, RVar, SymGA),
    replace_nth0(Args, J, RVar, ConcGA),
    run_goal(opts(20000, false, InputVarIds), Prog, comp(RN, SymGA), 900002, Str),
    take_events(200, Str, Evs),
    findall(S, member(ans(S), Evs), SymAnswers),
    findall(E, member(err(E), Evs), SymErr),
    atom_concat(Name, '__in', InN),
    replace_nth0(SymArgs, J, CVar, HeadC),
    replace_nth0(SymArgs, J, comp(c, [CVar]), WArgs),
    Wrapper = clause(comp(InN, HeadC), comp(RN, WArgs), 900002),
    if_commit(( SymErr == [], SymAnswers = [S], inputs_untouched(S, InputVarIds),
                resolve(RVar, S, comp(c, [Val0])) ),
              ( unalias_inputs(S, InputVarIds, SymArgs, Val0, Val),
                replace_nth0(SymArgs, J, Val, HeadV),
                Clause = clause(comp(InN, HeadV), atom(true), 900002),
                substitute_inputs(TextInputs, Val, Value),
                depends(Val, D),
                string_concat("input characters ", D, How) ),
    if_commit(( SymErr == [], SymAnswers = [S], resolve(RVar, S, atom(none)) ),
              ( Value = nothing, Clause = Wrapper,
                format(string(How), "no character ~d for inputs of this length", [K]) ),
              ( Clause = Wrapper,
                why(SymErr, SymAnswers, Why),
                first_value(Prog, comp(RN, ConcGA), 900002, RVar, CE),
                if_commit(CE = left(EM),
                          ( Value = nothing, format(string(How), "~w; error: ~w", [Why, EM]) ),
                          ( CE = right(MV), value_of(MV, Value), How = Why )) ))).

why(SymErr, SymAnswers, Why) :-
    if_commit(SymErr = [E|_],
              ( first_line(E, L), format(string(Why), "computes on character values (~w)", [L]) ),
              if_commit(SymAnswers = [_, _|_],
                        Why = "not unique on input character variables (several answers)",
                        Why = "depends on character values")).

first_line(E, L) :-
    if_commit(sub_string(E, B, _, _, "\n"), once_det(sub_string(E, 0, B, _, L)), L = E).

value_of(MV, V) :-
    if_commit(MV = just(comp(c, [X])), V = just(X), V = nothing).

%  every input character variable is still an unbound variable, and no two
%  of them were made equal
inputs_untouched(S, Ids) :-
    findall(W, ( member(V, Ids), walk(var(V, ''), S, W) ), Ws),
    findall(I, member(var(I, _), Ws), WIds),
    same_length(WIds, Ws),
    sort(WIds, SW),
    same_length(SW, Ws).

unalias_inputs(S, Ids, SymArgs, T, T1) :-
    if_commit(T = var(W, _),
              if_commit(( member(V, Ids), walk(var(V, ''), S, var(W1, _)), W1 =:= W ),
                        ( input_var_name(SymArgs, V, Nm), T1 = var(V, Nm) ),
                        T1 = T),
              if_commit(T = comp(F, As),
                        ( maplist(unalias_inputs(S, Ids, SymArgs), As, Bs), T1 = comp(F, Bs) ),
                        T1 = T)).

input_var_name(SymArgs, V, Nm) :-
    if_commit(( member(A, SymArgs), term_vars_ordered(A, Vs), member(var(W, Nm0), Vs), W =:= V ),
              Nm = Nm0, Nm = 'I').

depends(Val, D) :-
    term_vars_ordered(Val, Vs),
    findall(N, member(var(_, N), Vs), Ns),
    if_commit(Ns == [], D = "none (constant or computed from non-text inputs)",
              ( atomic_list_concat(Ns, ', ', DA), atom_string(DA, D) )).

chars_of(T, M) :-
    if_commit(T == atom('[]'), M = just([]),
              if_commit(( T = comp('.', [H, R]), char_elem(H) ),
                        ( chars_of(R, M0), maybe_cons(M0, H, M) ),
                        M = nothing)).

char_elem(H) :-
    if_commit(( H = atom(A), atom_length(A, 1) ), true, H = int(_)).

elements_of(T, M) :-
    if_commit(( T = atom(A), A \== '[]' ),
              ( atom_chars(A, Cs), maplist(wrap_atom, Cs, Xs), M = just(Xs) ),
              if_commit(T = int(I),
                        ( number_codes(I, Codes), atom_codes(IA, Codes), atom_chars(IA, Cs),
                          maplist(wrap_atom, Cs, Xs), M = just(Xs) ),
                        list_elems(T, M))).

list_elems(T, M) :-
    if_commit(T == atom('[]'), M = just([]),
              if_commit(T = comp('.', [H, R]),
                        ( list_elems(R, M0), maybe_cons(M0, H, M) ),
                        M = nothing)).

substitute_inputs(Inputs, Val, M) :-
    length(Inputs, NI),
    findall(Id-C, ( member(I-Cs, Inputs), numbered_list(Cs, 1, QCs), member(Q-C, QCs),
                    Id is 1000 * (I + 1) + Q ), Table),
    findall(Nm-C, ( member(I-Cs, Inputs), numbered_list(Cs, 1, QCs), member(Q-C, QCs),
                    input_name(NI, I, Q, Nm) ), ByName),
    sub_inputs(Table, ByName, Val, M).

sub_inputs(Table, ByName, T, M) :-
    if_commit(T = var(V, Nm),
              if_commit(memberchk(V-C, Table), M = just(C),
                        if_commit(memberchk(Nm-C2, ByName), M = just(C2), M = nothing)),
              if_commit(T = comp(F, As),
                        ( maplist(sub_inputs(Table, ByName), As, Ms),
                          if_commit(maplist(is_just_v, Ms, Bs), M = just(comp(F, Bs)), M = nothing) ),
                        M = just(T))).

is_just_v(just(X), X).

show_char_c(T, S) :-
    if_commit(( T = atom(A), atom_length(A, 1) ), S = A,
              if_commit(( T = int(I), I >= 0, I < 1114112 ), char_code(S, I),
                        show_term_q(T, S))).

% ---------------------------------------------------------------------------
% formula: closed forms per position

formula_cmd(Fl, File, KeyS, N) :-
    load_cut_free(File, P, Evs),
    parse_key(KeyS, Key),
    fl_domain(Fl, MD),
    if_commit(MD = just(Lo-Hi), true, die("formula needs --domain LO..HI")),
    out_pos(Fl, Key, J),
    fl_domain_arg(Fl, DA),
    D is DA - 1,
    slice_positions(P, Key, J, N, SR),
    generated(P, SR, Key, J, N, [], Base),
    with_prelude(Base, Prog),
    sr_steps(SR, SSteps),
    proved(P, SSteps, Base, _),
    fl_mnns(Fl, MM),
    if_commit(MM = just(Dir), MDir = just(Dir),
              if_commit(getenv('MNNS_DIR', EDir), MDir = just(EDir), MDir = nothing)),
    findall(K, between(1, N, K), Ks),
    maplist(formula_position(Prog, SR, Key, J, D, Lo, Hi, MDir), Ks, ChosenL),
    concat_lists(ChosenL, Chosen),
    findall(C, ( member(ch(Sp, F, IsCodes), Chosen), formula_clause(Sp, F, IsCodes, Lo, Hi, D, C) ), FCls),
    findall(comp(formula_step, [ST, int(Lo), int(Hi), int(D), comp(':-', [H, B])]),
            ( member(ch(Sp, F, IsCodes), Chosen), spec_term(Sp, ST),
              formula_clause(Sp, F, IsCodes, Lo, Hi, D, clause(H, B, _)) ), FSteps),
    conc(SSteps, FSteps, Steps),
    generated(P, SR, Key, J, N, FCls, ProgOut),
    proved(P, Steps, ProgOut, Report),
    conc(Evs, Report, HL),
    header(File, HL, SR, Hdr0),
    atomic_list_concat([Hdr0,
                        "% Positions with a formula are exact on the domain by exhaustion (checked in the\n",
                        "% proof) and use the sliced program (NAME__charK__r) outside it.\n"], Hdr),
    write_out(Fl, Hdr, ProgOut, Steps).

formula_position(Prog, SR, Key, J, D, Lo, Hi, MDir, K, Chosen) :-
    Sp = spec(Key, J, K),
    r_name(Sp, RN),
    sr_used(SR, UMap),
    map_find(UMap, Sp, [], Used),
    Key = _/Arity,
    if_commit(ord_subset(Used, [D]),
              ( findall(S, ( between(Lo, Hi, X), formula_sample(Prog, RN, Arity, J, D, X, S) ), Samples),
                if_commit(maplist(code_of, Samples, Codes),
                          formula_found(Sp, K, Lo, Codes, Samples, MDir, Chosen),
                          ( format("char ~d: not defined on all of ~d..~d; kept as sliced code~n", [K, Lo, Hi]),
                            Chosen = [] )) ),
              ( findall(U1, ( member(U, Used), U1 is U + 1 ), Us1),
                show_int_list(Us1, UL),
                format("char ~d: uses other inputs too ~w; kept as sliced code~n", [K, UL]),
                Chosen = [] )).

show_int_list(Is, S) :-
    atomic_list_concat(Is, ',', A),
    format(string(S), "[~w]", [A]).

formula_sample(Prog, RN, Arity, J, D, X, S) :-
    A1 is Arity - 1,
    findall(A, ( between(0, A1, I), sample_arg(I, J, D, X, A) ), Args),
    NV is Arity + 2,
    first_value(Prog, comp(RN, Args), NV, var(0, 'R'), E),
    if_commit(E = right(M), S = M, S = nothing).

sample_arg(I, J, D, X, A) :-
    if_commit(I =:= J, A = var(0, 'R'),
              if_commit(I =:= D, A = int(X), ( I1 is I + 1, A = var(I1, '_') ))).

code_of(S, C) :-
    if_commit(( S = just(comp(c, [atom(A)])), atom_length(A, 1) ), char_code(A, C),
              S = just(comp(c, [int(C)]))).

formula_found(Sp, K, Lo, Codes, Samples, MDir, Chosen) :-
    infer_native(Codes, Native),
    if_commit(MDir = just(Dir),
              ( infer_with_mnns(Dir, Codes, ME),
                if_commit(ME = right(F0), ( Formula = F0, Source = "mnns AlgebraPLOp" ),
                          ( ME = left(Why), Formula = Native,
                            format(string(Source), "native mirror of mnns AlgebraPLOp (~w)", [Why]) )) ),
              ( Formula = Native, Source = "native mirror of mnns AlgebraPLOp (no mnns given)" )),
    if_commit(( Formula = just(F), numbered_list(Codes, 0, PCs), maplist(formula_fits(F), PCs) ),
              ( show_formula(F, FS),
                if_commit(Native == just(F), Diff = "", Diff = "; differs from native mirror"),
                format("char ~d: code = ~w at P = N - ~d   [~w~w]~n", [K, FS, Lo, Source, Diff]),
                is_code_list(Samples, IsCodes),
                Chosen = [ch(Sp, F, IsCodes)] ),
              ( format("char ~d: no formula (~w); kept as sliced code~n", [K, Source]),
                Chosen = [] )).

formula_fits(F, P-C) :-
    eval_formula(F, P, V),
    V =:= C.

is_code_list(Samples, B) :-
    test(Samples = [just(comp(c, [int(_)]))|_], B).

%  NAME__charK(..., N, ..., C) :- ( integer(N), Lo =< N =< Hi -> formula ; sliced ).
formula_clause(Sp, F, IsCodes, Lo, Hi, D, clause(comp(Name, Args), Body, 20)) :-
    Sp = spec(_/Arity, J, _),
    spec_name(Sp, Name),
    r_name(Sp, RN),
    NV = var(0, 'N'),
    CV = var(1, 'C'),
    PV = var(2, 'P'),
    CodeV = var(3, 'Code'),
    A1 is Arity - 1,
    findall(A, ( between(0, A1, I), fclause_arg(I, J, D, NV, CV, A) ), Args),
    replace_nth0(Args, J, comp(c, [CV]), ArgsR),
    mk_conj([comp(integer, [NV]), comp('>=', [NV, int(Lo)]), comp('=<', [NV, int(Hi)])], Guard),
    formula_expr(F, PV, FE),
    if_commit(IsCodes == true, Last = comp('=', [CV, CodeV]), Last = comp(char_code, [CV, CodeV])),
    mk_conj([comp(is, [PV, comp('-', [NV, int(Lo)])]), comp(is, [CodeV, FE]), Last], Compute),
    Body = comp(';', [comp('->', [Guard, Compute]), comp(RN, ArgsR)]).

fclause_arg(I, J, D, NV, CV, A) :-
    if_commit(I =:= J, A = CV,
              if_commit(I =:= D, A = NV, ( I10 is 10 + I, A = var(I10, '_') ))).
