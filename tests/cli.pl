/*  cli.pl - end-to-end tests of the plop2 command line (port of the Haskell
    tests/Cli.hs).

    swipl tests/cli.pl          (after building build/plop2 and build/detlog2)

    Each test runs build/plop2 (or build/detlog2) and looks at what it printed (standard
    output, then standard error) or at a file it wrote.
*/

:- use_module(library(process)).

relation(_).
:- relation(candidate_dir/2).

candidate_dir(_, D) :- getenv('DETLOG2_DIR', D).
candidate_dir(Here, D) :- atom_concat(Here, '/../../detlog2', D), exists_directory(D).
candidate_dir(Here, D) :- atom_concat(Here, '/../build/detlog2-src', D), exists_directory(D).

:- prolog_load_context(directory, Here), findall(D, candidate_dir(Here, D), [Dir|_]),
   asserta(user:file_search_path(detlog2, Dir)).

:- use_module(detlog2(src/detlog_runtime)).
:- initialization(main, main).

binary(plop2, './build/plop2').
binary(detlog2, './build/detlog2').

main :-
    actions(As),
    foldl(run_action, As, 0, Fails),
    format("~n"),
    compare(O, Fails, 0),
    finish(O, Fails).

finish(=, _) :-
    format("all CLI tests passed~n").
finish(>, N) :-
    format("~d CLI test(s) failed~n", [N]),
    halt(1).

out(Args, Text) :-
    out(plop2, Args, Text).

out(Which, Args, Text) :-
    binary(Which, Bin),
    process_create(Bin, Args, [stdout(pipe(O)), stderr(pipe(E)), process(Pid)]),
    read_string(O, _, OS),
    read_string(E, _, ES),
    close(O),
    close(E),
    process_wait(Pid, _),
    string_concat(OS, ES, Text).

report(true, Name, _, F, F) :-
    format("PASS ~w~n", [Name]).
report(false, Name, Detail, F0, F) :-
    format("FAIL ~w~n", [Name]),
    split_string(Detail, "\n", "", Ls),
    forall_detail(Ls),
    F is F0 + 1.

forall_detail([]).
forall_detail([L|Ls]) :-
    format("    ~s~n", [L]),
    forall_detail(Ls).

contains(S, Sub, B) :-
    test_b(sub_string(S, _, _, _, Sub), B).

test_b(G, B) :-
    if_commit(G, B = true, B = false).

run_action(A, F0, F) :-
    action_kind(A, K),
    run_kind(K, A, F0, F).

action_kind(A, K) :-
    functor(A, K, _).

run_kind(expect, expect(Name, Want, Args), F0, F) :-
    out(Args, O),
    contains(O, Want, B),
    report(B, Name, O, F0, F).
run_kind(exact, exact(Name, Want, Args), F0, F) :-
    out(Args, O0),
    string_codes(O0, Cs),
    reverse(Cs, R),
    drop_newlines(R, R1),
    reverse(R1, Cs1),
    string_codes(O, Cs1),
    test_b(O == Want, B),
    format(string(D), "wanted:~n~s~ngot:~n~s", [Want, O]),
    report(B, Name, D, F0, F).
run_kind(file_has, file_has(Name, Want, Path), F0, F) :-
    read_file_to_string(Path, S, []),
    contains(S, Want, B),
    report(B, Name, S, F0, F).
run_kind(expect_d2, expect_d2(Name, Want, Args), F0, F) :-
    out(detlog2, Args, O),
    contains(O, Want, B),
    report(B, Name, O, F0, F).
run_kind(file_lacks, file_lacks(Name, Bad, Path), F0, F) :-
    read_file_to_string(Path, S, []),
    contains(S, Bad, B0),
    neg_bool(B0, B),
    report(B, Name, S, F0, F).
run_kind(run, run(Args), F, F) :-
    out(Args, _).
run_kind(code_free, code_free(Name, Path, Banned), F0, F) :-
    read_file_to_string(Path, S, []),
    split_string(S, "\n", "", Ls),
    findall(L, ( member(L, Ls), if_commit(sub_string(L, 0, 1, _, "%"), fail, true) ), Code),
    atomic_list_concat(Code, '\n', CA),
    atom_string(CA, CS),
    test_b(( member(X, Banned), sub_string(CS, _, _, _, X) ), Found),
    neg_bool(Found, B),
    report(B, Name, CS, F0, F).
run_kind(replace, replace(Src, Dst, Old, New), F, F) :-
    read_file_to_string(Src, S, []),
    replace_first(S, Old, New, S1),
    setup_call_cleanup(open(Dst, write, W, [encoding(utf8)]), write(W, S1), close(W)).
run_kind(mnns, mnns, F0, F) :-
    if_commit(( getenv('MNNS_DIR', Dir), absolute_file_name(path(swipl), _, [access(execute), file_errors(fail)]) ),
              run_action(expect('formula: found by mnns', "[mnns AlgebraPLOp]",
                                [formula, 'examples/numbers.pl', 'letter/2', '1', '--domain', '0..20', '--mnns', Dir]),
                         F0, F),
              ( format("SKIP mnns formula (swipl or MNNS_DIR missing)~n"), F = F0 )).

run_kind(write_file, write_file(Path, Text), F, F) :-
    run_kind_write(Path, Text).

neg_bool(true, false).
neg_bool(false, true).

drop_newlines([], []).
drop_newlines([C|Cs], Out) :-
    if_commit(C =:= 0'\n, drop_newlines(Cs, Out), Out = [C|Cs]).

replace_first(S, Old, New, S1) :-
    string_codes(S, Cs),
    string_codes(Old, OCs),
    string_codes(New, NCs),
    if_commit(( append(Before, Rest, Cs), append(OCs, After, Rest) ),
              ( conc(Before, NCs, P1), conc(P1, After, R), string_codes(S1, R) ),
              S1 = S).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

actions([
  % separate programs per position
  run([chars, 'examples/greet.pl', 'greet/2', '3', '-o', 'build/greet3.pl']),
  file_has('chars: char1 program', "greet__char1__alt(_, R)", 'build/greet3.pl'),
  file_has('chars: char3 program', "greet__char3__alt(_, R)", 'build/greet3.pl'),
  file_lacks('chars: the output-building append is not kept', "append(", 'build/greet3.pl'),
  file_has('chars: proof accepted', "proof accepted", 'build/greet3.pl'),
  expect('proof-check: accepted from files', "proof accepted",
         ['proof-check', 'examples/greet.pl', 'build/greet3.pl', 'build/greet3.pl.proof']),
  replace('build/greet3.pl', 'build/greet3_bad.pl', "c('H')", "c('J')"),
  expect('proof-check: tampered code rejected', "proof rejected",
         ['proof-check', 'examples/greet.pl', 'build/greet3_bad.pl', 'build/greet3.pl.proof']),
  run([chars, 'examples/greet.pl', 'double/2', '3', '-o', 'build/double3.pl']),
  file_has('chars: double char3 calls char1''s program on the tail', "double__char1__r(Xs, R)", 'build/double3.pl'),
  file_has('chars: double char1 has no tail variable', "double__char1__alt([X|_], R)", 'build/double3.pl'),
  file_has('chars: an empty output answers none', "double__char1__alt([], R)", 'build/double3.pl'),

  % the dropped-goal bug: a clause whose output is too short answers none
  expect('run: first answer has no char 2, so none (no later answer)', "char 2: -",
         [run, 'examples/greet.pl', 'short(x, Out)', '2']),
  expect('run: short matches', "match: every position agrees", [run, 'examples/greet.pl', 'short(x, Out)', '2']),
  % a goal that may fail is kept, not dropped
  expect('run: a guard on other data is kept', "match: every position agrees",
         [run, 'examples/greet.pl', 'guarded("ab", Out)', '3']),
  expect('run: guard failure is respected', "match: every position agrees",
         [run, 'examples/greet.pl', 'guarded("abcdef", Out)', '3']),

  % run on input character variables
  expect('run: greet matches', "match: every position agrees", [run, 'examples/greet.pl', 'greet("bob", Out)', '12']),
  expect('run: greet char 8 is input char 1', "char 8: b   (input characters I1)",
         [run, 'examples/greet.pl', 'greet("bob", Out)', '12']),
  expect('run: greet char 1 is a constant', "char 1: 'H'   (input characters none",
         [run, 'examples/greet.pl', 'greet("bob", Out)', '12']),
  expect('run: greet past the end', "char 12: -", [run, 'examples/greet.pl', 'greet("bob", Out)', '12']),
  expect('run: proof accepted', "proof accepted", [run, 'examples/greet.pl', 'greet("bob", Out)', '12']),
  expect('run: double', "char 3: b   (input characters I2)", [run, 'examples/greet.pl', 'double("abc", Out)', '6']),
  expect('run: double matches', "match: every position agrees", [run, 'examples/greet.pl', 'double("abc", Out)', '6']),
  expect('run: backwards', "char 1: c   (input characters I3)", [run, 'examples/greet.pl', 'backwards("abc", Out)', '3']),
  expect('run: shout computes on values', "computes on character values", [run, 'examples/greet.pl', 'shout("abc", Out)', '3']),
  expect('run: shout matches', "match: every position agrees", [run, 'examples/greet.pl', 'shout("abc", Out)', '3']),
  expect('run: tag (cut) matches', "match: every position agrees", [run, 'examples/greet.pl', 'tag("ab", Out)', '4']),
  expect('run: tag empty matches', "match: every position agrees", [run, 'examples/greet.pl', 'tag([], Out)', '5']),
  expect('run: square matches', "match: every position agrees", [run, 'examples/numbers.pl', 'square(12, Out)', '4']),
  expect('run: input must be given', "must be given", [run, 'examples/greet.pl', 'greet(X, Out)', '3']),
  run([run, 'examples/greet.pl', 'greet("bob", Out)', '11', '-o', 'build/greet_in.pl']),
  file_has('run: per-position input-variable programs', "greet__char8__in([I1, _, _], I1).", 'build/greet_in.pl'),
  expect('proof-check: input-character facts re-checked symbolically', "proof accepted",
         ['proof-check', 'examples/greet.pl', 'build/greet_in.pl', 'build/greet_in.pl.proof']),
  replace('build/greet_in.pl', 'build/greet_in_bad.pl',
          "greet__char8__in([I1, _, _], I1).", "greet__char8__in([_, I2, _], I2)."),
  replace('build/greet_in.pl.proof', 'build/greet_in_bad.pl.proof',
          "input_chars_step(spec(greet/2, 1, 8), greet__char8__in([",
          "input_chars_step(spec(greet/2, 1, 8), greet__char8__in([_, "),
  expect('proof-check: a wrong input-character fact is rejected', "proof rejected",
         ['proof-check', 'examples/greet.pl', 'build/greet_in_bad.pl', 'build/greet_in.pl.proof']),

  % formulas through mnns AlgebraPLOp
  expect('formula: linear code', "char 1: code = linear(1, 97)",
         [formula, 'examples/numbers.pl', 'letter/2', '3', '--domain', '0..20']),
  expect('formula: constant', "char 3: code = constant(120)",
         [formula, 'examples/numbers.pl', 'letter/2', '3', '--domain', '0..20']),
  expect('formula: none for first digit of a square', "char 1: no formula",
         [formula, 'examples/numbers.pl', 'square/2', '1', '--domain', '1..12']),
  mnns,
  run([formula, 'examples/numbers.pl', 'letter/2', '3', '--domain', '0..20', '-o', 'build/letter.pl']),
  file_has('formula: guarded formula clause', "integer(N)", 'build/letter.pl'),
  file_has('formula: sliced program outside the domain', "letter__char1__r(N, c(C))", 'build/letter.pl'),
  file_has('formula: char 2 drops char 1''s computation with certificates', "total(arith)", 'build/letter.pl.proof'),
  expect('proof-check: formulas re-checked by evaluation', "proof accepted",
         ['proof-check', 'examples/numbers.pl', 'build/letter.pl', 'build/letter.pl.proof']),
  replace('build/letter.pl.proof', 'build/letter_bad.proof', "total(arith)", "total(text)"),
  expect('proof-check: a wrong certificate is rejected', "proof rejected",
         ['proof-check', 'examples/numbers.pl', 'build/letter.pl', 'build/letter_bad.proof']),
  replace('build/letter.pl', 'build/letter_bad.pl', "1 * P + 97", "1 * P + 98"),
  replace('build/letter.pl.proof', 'build/letter_bad2.proof', "1 * P + 97", "1 * P + 98"),
  expect('proof-check: a wrong formula is rejected', "proof rejected",
         ['proof-check', 'examples/numbers.pl', 'build/letter_bad.pl', 'build/letter_bad2.proof']),

  % generated files run on detlog2 (cut-free)
  expect_d2('detlog2 runs letter formula', "C = d.", [run, 'build/letter.pl', 'letter__char1(3, C)']),
  expect_d2('detlog2 runs letter outside the domain', "C = z.", [run, 'build/letter.pl', 'letter__char1(25, C)']),
  expect_d2('detlog2 runs greet char 9', "C = o.", [run, 'build/greet_in.pl', 'greet__char9("bob", C)'])
]).
