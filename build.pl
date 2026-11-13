/*  build.pl - build and test plop2.

    swipl build.pl            build build/plop2 (a saved state)
    swipl build.pl test       build, check that every Prolog source is
                              cut-free and choicepoint-free (with detlog2's
                              tools/cutfree.pl), then run the end-to-end tests
    swipl build.pl ci         as test, fetching detlog2 and mnns first when
                              DETLOG2_DIR and MNNS_DIR are not set, then check
                              the 200 recorded inputs and outputs
    swipl build.pl ios        run the 200 inputs and write io/ios.txt
    swipl build.pl check-ios  run them again and fail if any output changed

    DETLOG2_DIR (default ../detlog2, else build/detlog2-src) selects detlog2.
    The Haskell version is built with runghc haskell/Build.hs.
*/

:- use_module(library(process)).

relation(_).
:- relation(candidate_dir/2).

candidate_dir(_, D) :-
    getenv('DETLOG2_DIR', D).
candidate_dir(Here, D) :-
    atom_concat(Here, '/../detlog2', D),
    exists_directory(D).
candidate_dir(Here, D) :-
    atom_concat(Here, '/build/detlog2-src', D),
    exists_directory(D).

%  detlog2 is needed before its runtime can be loaded: clone it when no
%  copy is found (findall/3 keeps this free of choicepoints and cuts).
:- prolog_load_context(directory, Here),
   findall(D, candidate_dir(Here, D), Ds),
   clone_if_none(Ds, Here, Dir),
   absolute_file_name(Dir, Abs),
   setenv('DETLOG2_DIR', Abs),
   asserta(user:file_search_path(detlog2, Abs)).

clone_if_none([D|_], _, D).
clone_if_none([], Here, D) :-
    atom_concat(Here, '/build/detlog2-src', D),
    make_directory_path('build'),
    process_create(path(git), [clone, '--depth', '1', 'https://github.com/luciangreen/detlog2', D], []).

:- use_module(detlog2(src/detlog_runtime)).

:- initialization(main, main).

main :-
    current_prolog_flag(argv, Argv),
    drop_dashes(Argv, Args),
    make_directory_path(build),
    swipl(['-o', 'build/plop2', '-c', 'plop2.pl']),
    mode(Args).

drop_dashes([], []).
drop_dashes([A|As], Fs) :-
    if_commit(A == '--', Fs = Fs1, Fs = [A|Fs1]),
    drop_dashes(As, Fs1).

mode(Args) :-
    if_commit(Args = [ci|_], ( fetch_mnns, tests, ios(check) ),
    if_commit(Args = [test|_], tests,
    if_commit(Args = [ios|_], ios(make),
    if_commit(Args = ['check-ios'|_], ios(check),
              true)))).

sources(['plop2.pl', 'build.pl', 'src/plop2_util.pl', 'src/slice.pl', 'src/formula.pl',
         'src/plop_proof.pl', 'src/plop2_cli.pl', 'tests/cli.pl', 'io/ios.pl']).

tests :-
    getenv('DETLOG2_DIR', D2),
    format(atom(Checker), "~w/tools/cutfree.pl", [D2]),
    format(atom(D2Main), "~w/detlog2.pl", [D2]),
    sources(Ss),
    swipl([Checker, '--'|Ss]),
    swipl(['-o', 'build/detlog2', '-c', D2Main]),
    swipl(['tests/cli.pl']).

ios(Mode) :-
    swipl(['io/ios.pl', Mode]).

%  CI: use $MNNS_DIR, or clone mnns next to the build.
fetch_mnns :-
    if_commit(getenv('MNNS_DIR', _),
              true,
              ( if_commit(exists_directory('build/mnns'),
                          true,
                          run(path(git), [clone, '--depth', '1', 'https://github.com/luciangreen/mnns', 'build/mnns'])),
                absolute_file_name('build/mnns', Abs),
                setenv('MNNS_DIR', Abs) )).

swipl(Args) :-
    run(path(swipl), Args).

run(Exe, Args) :-
    process_create(Exe, Args, [process(Pid)]),
    process_wait(Pid, Status),
    if_commit(Status == exit(0), true,
              ( format(user_error, "build: ~w ~w failed (~w)~n", [Exe, Args, Status]), halt(1) )).
