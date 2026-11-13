/*  ios.pl - 200 inputs and the outputs they give, from real runs of
    plop2 (port of the Haskell io/Ios.hs).

    swipl io/ios.pl make           runs the 200 inputs and writes io/ios.txt
    swipl io/ios.pl check          runs them again and fails if any output changed
    swipl io/ios.pl write FILE     writes the outputs to FILE
    swipl io/ios.pl compare FILE   checks that io/ios.txt and FILE record the
                                   same outputs (the header line aside), for
                                   the Haskell recording haskell/io/ios.txt

    The inputs are made the same way every time (see case_for/2).  Each
    output is everything the command printed (standard output, then
    standard error), with its exit code when that is not 0.
*/

relation(_).
:- relation(candidate_dir/2).

candidate_dir(_, D) :- getenv('DETLOG2_DIR', D).
candidate_dir(Here, D) :- atom_concat(Here, '/../../detlog2', D), exists_directory(D).
candidate_dir(Here, D) :- atom_concat(Here, '/../build/detlog2-src', D), exists_directory(D).

:- prolog_load_context(directory, Here), findall(D, candidate_dir(Here, D), [Dir|_]),
   asserta(user:file_search_path(detlog2, Dir)).

:- use_module(detlog2(src/detlog_runtime)).
:- use_module(library(process)).

:- initialization(main, main).

title(plop2).
binary('./build/plop2').

main :-
    current_prolog_flag(argv, Argv),
    drop_dashes(Argv, Args),
    if_commit(Args = [compare, Other], compare_files(Other), run_and_render(Args)).

compare_files(Other) :-
    read_file_to_string("io/ios.txt", A, [encoding(utf8)]),
    read_file_to_string(Other, B, [encoding(utf8)]),
    split_string(A, "\n", "", [_|AL]),
    split_string(B, "\n", "", [_|BL]),
    if_commit(AL == BL,
              format("io/ios.txt and ~w record the same 200 outputs.~n", [Other]),
              ( differing(AL, BL, 2, Ds), take(20, Ds, D20), maplist(show_diff, D20),
                format("io/ios.txt and ~w differ.~n", [Other]), halt(1) )).

run_and_render(Args) :-
    run_all(Outs),
    render(Outs, Text),
    ios_mode(Args, Text).

drop_dashes([], []).
drop_dashes([A|As], Fs) :-
    if_commit(A == '--', Fs = Fs1, Fs = [A|Fs1]),
    drop_dashes(As, Fs1).

ios_mode(Args, Text) :-
    if_commit(Args = [make],
              ( write_text("io/ios.txt", Text), format("wrote io/ios.txt (200 inputs and outputs)~n") ),
    if_commit(Args = [check],
              check_text(Text),
    if_commit(Args = [write, File],
              write_text(File, Text),
              ( format("usage: ios make | ios check | ios write FILE~n"), halt(2) )))).

write_text(File, Text) :-
    setup_call_cleanup(open(File, write, S, [encoding(utf8)]), write(S, Text), close(S)).

check_text(Text) :-
    read_file_to_string("io/ios.txt", Old, [encoding(utf8)]),
    if_commit(Old == Text,
              format("All 200 inputs give the outputs in io/ios.txt.~n"),
              ( split_string(Old, "\n", "", OL),
                split_string(Text, "\n", "", NL),
                differing(OL, NL, 1, Ds),
                take(20, Ds, D20),
                maplist(show_diff, D20),
                format("Outputs differ from io/ios.txt. If the change is meant, run swipl io/ios.pl make and commit io/ios.txt.~n"),
                halt(1) )).

differing([], _, _, []).
differing([A|As], Bs, N, Ds) :-
    differing_(Bs, A, As, N, Ds).

differing_([], _, _, _, []).
differing_([B|Bs], A, As, N, Ds) :-
    N1 is N + 1,
    differing(As, Bs, N1, Ds1),
    if_commit(A == B, Ds = Ds1, Ds = [N-A-B|Ds1]).

show_diff(N-A-B) :-
    format("line ~d:~n  recorded: ~s~n  now:      ~s~n", [N, A, B]).

take(N, L, T) :-
    compare(O, N, 0),
    take_(O, N, L, T).

take_(<, _, _, []).
take_(=, _, _, []).
take_(>, N, L, T) :-
    take_list(L, N, T).

take_list([], _, []).
take_list([X|Xs], N, [X|T]) :-
    N1 is N - 1,
    take(N1, Xs, T).

nth0_det(I, [X|Xs], Y) :-
    compare(O, I, 0),
    nth0_(O, I, X, Xs, Y).

nth0_(=, _, X, _, X).
nth0_(>, I, _, Xs, Y) :-
    I1 is I - 1,
    nth0_det(I1, Xs, Y).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

% ---------------------------------------------------------------------------
% The 200 inputs

%  Choose element i (from the case number k and a salt) of a list.
pick(K, Salt, Xs, X) :-
    length(Xs, L),
    I is (K * (2 * Salt + 1) + Salt * 7) mod L,
    nth0_det(I, Xs, X).

%  A list of length n from a pool, starting at a place set by k.
pick_n(K, Salt, N, Xs, Out) :-
    length(Xs, L),
    Start is (K * (Salt + 3)) mod L,
    findall(X, ( between(1, N, J), I is (Start + J - 1) mod L, nth0_det(I, Xs, X) ), Out).

show_list(Xs, S) :-
    atomic_list_concat(Xs, ',', A),
    format(string(S), "[~w]", [A]).

texts(["bob", "al", "zoe", "kim", "ed", "abc", "x", "lucian", "mnn", "ok", "prolog", "", "aa", "abcdef"]).

%  Haskell's show of a text: the text in double quotes.
str(K, Salt, S) :-
    texts(Ts),
    pick(K, Salt, Ts, T),
    format(string(S), "\"~s\"", [T]).

case_for(K, Args) :-
    C is K mod 10,
    case_args(C, K, Args).

case_args(0, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 1, S), format(string(Q), "greet(~s, Out)", [S]), num(1 + K mod 12, N).
case_args(1, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 2, S), format(string(Q), "double(~s, Out)", [S]), num(1 + K mod 8, N).
case_args(2, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 3, S), format(string(Q), "backwards(~s, Out)", [S]), num(1 + K mod 6, N).
case_args(3, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 4, S), format(string(Q), "tag(~s, Out)", [S]), num(1 + K mod 9, N).
case_args(4, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 5, S), format(string(Q), "guarded(~s, Out)", [S]), num(1 + K mod 9, N).
case_args(5, K, ["run", "examples/numbers.pl", Q, N]) :-
    A is K mod 40, format(string(Q), "square(~d, Out)", [A]), num(1 + K mod 5, N).
case_args(6, K, ["run", "examples/greet.pl", Q, N]) :-
    str(K, 7, S), format(string(Sh), "shout(~s, Out)", [S]),
    pick(K, 6, ["short(x, Out)", Sh], Q), num(1 + K mod 4, N).
case_args(7, K, ["run", "examples/numbers.pl", Q, N]) :-
    A is K mod 26, format(string(Q), "letter(~d, Out)", [A]), num(1 + K mod 4, N).
case_args(8, K, ["formula", "examples/numbers.pl", "letter/2", N, "--domain", D]) :-
    num(1 + K mod 3, N),
    Lo is K mod 5, Hi is K mod 5 + 5 + K mod 7,
    format(string(D), "~d..~d", [Lo, Hi]).
case_args(9, K, ["chars", "examples/greet.pl", P, N]) :-
    pick(K, 8, ["greet/2", "double/2", "tag/2", "guarded/2", "short/2"], P),
    num(1 + K mod 3, N).

num(E, S) :-
    V is E,
    number_string(V, S).

run_all(Outs) :-
    unsetenv('MNNS_DIR'),
    numlist(1, 200, Ks),
    maplist(run_case_k, Ks, Outs).

run_case_k(K, Args-Out) :-
    case_for(K, Args),
    run_case(Args, Out).

run_case(Args, Out) :-
    binary(Bin),
    process_create(Bin, Args, [stdout(pipe(O)), stderr(pipe(E)), process(Pid)]),
    read_string(O, _, OS),
    read_string(E, _, ES),
    close(O),
    close(E),
    process_wait(Pid, Status),
    string_concat(OS, ES, All),
    trim_end(All, Text),
    code_line(Status, CL),
    string_concat(Text, CL, Out).

code_line(Status, CL) :-
    if_commit(Status == exit(0),
              CL = "",
              if_commit(Status = exit(N),
                        format(string(CL), "\n(exit code ~d)", [N]),
                        format(string(CL), "\n(~w)", [Status]))).

trim_end(S, T) :-
    string_codes(S, Cs),
    reverse(Cs, R),
    drop_blank(R, R1),
    reverse(R1, Cs1),
    string_codes(T, Cs1).

drop_blank([], []).
drop_blank([C|Cs], Out) :-
    if_commit(memberchk(C, [0' , 0'\n]), drop_blank(Cs, Out), Out = [C|Cs]).

quote_arg(A, Q) :-
    string_codes(A, Cs),
    if_commit(( Cs \== [], plain_arg(Cs) ),
              Q = A,
              ( foldl(quote_code, Cs, [], RevQ),
                reverse(RevQ, QCs),
                conc([0'\'|QCs], [0'\'], All),
                string_codes(Q, All) )).

plain_arg([]).
plain_arg([C|Cs]) :-
    if_commit(code_type(C, alnum), true, memberchk(C, `/._-`)),
    plain_arg(Cs).

quote_code(C, Acc, Out) :-
    if_commit(C =:= 0'\',
              Q = `'\\''`,
              Q = [C]),
    reverse(Q, RQ),
    conc(RQ, Acc, Out).

render(Outs, Text) :-
    title(T),
    format(string(H), "~w: 200 inputs and outputs, from real runs (swipl io/ios.pl make writes this file; swipl io/ios.pl check checks it).", [T]),
    numlist(1, 200, Ks),
    maplist(render_case, Ks, Outs, Blocks),
    conc([H|Blocks], ["\n"], Parts),
    atomic_list_concat(Parts, '', A),
    atom_string(A, Text).

render_case(I, Args-Out, Block) :-
    title(T),
    maplist(quote_arg, Args, QArgs),
    atomic_list_concat([T|QArgs], ' ', Cmd),
    split_string(Out, "\n", "", Lines),
    out_lines(Lines, Body),
    format(string(Block), "~n~n~d. ~w~n~s", [I, Cmd, Body]).

out_lines([L|Ls], Body) :-
    if_commit(( L == "", Ls == [] ),
              Body = "   => (no output)",
              ( maplist(indent_line, Ls, ILs),
                atomic_list_concat(["   => ", L|ILs], '', A),
                atom_string(A, Body) )).

indent_line(L, S) :-
    format(string(S), "~n      ~s", [L]).
