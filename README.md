# plop2

plop2 writes **one separate program per output character** of an algorithm.
Each program, `p__charK`, computes only character K: nothing for characters
1..K-1 or K+1..n, and no variables for the other data. Given n, plop2 runs
these n finite programs and checks them against the original algorithm.

It is built on [detlog2](https://github.com/luciangreen/detlog2): the reader,
the cut-free interpreter, and cut elimination. Closed forms come from
[mnns](https://github.com/luciangreen/mnns)'s AlgebraPLOp.

## Build

plop2 is written in cut-free, choicepoint-free SWI-Prolog: no `!`, `;`,
`->`, `\+`, `once/1` or `forall/2` in its source. A decision is
`if_commit/3` (from detlog2's `src/detlog_runtime.pl`), which takes the first
answer of its condition with `findall/3` + `limit/2`, and generators are only
called inside `findall/3`, an `if_commit/3` condition or `once_det/1`.
detlog2's `tools/cutfree.pl` checks every source file in the build.

```sh
git clone https://github.com/luciangreen/detlog2 ../detlog2   # or set DETLOG2_DIR
swipl build.pl             # builds build/plop2 (a saved state)
swipl build.pl test        # builds, runs the cut-free check and tests/cli.pl
swipl build.pl ci          # as test (cloning detlog2 and mnns if needed), then
                           # checks the 200 recorded runs in io/ios.txt
swipl plop2.pl chars examples/greet.pl greet/2 3   # or run from source
```

The Haskell version it was ported from is kept in `haskell/`
(`runghc haskell/Build.hs test`). CI builds both and checks that they record
the same 200 outputs (`swipl io/ios.pl compare haskell/io/ios.txt`).

Layout:

- `plop2.pl` - loader and `main`; loads detlog2's Prolog sources
- `src/slice.pl` - the per-position slicer (port of `Plop2.Slice`)
- `src/plop_proof.pl` - the independent proof checker (port of `Plop2.Proof`)
- `src/formula.pl` - closed forms and the mnns AlgebraPLOp bridge
- `src/plop2_cli.pl` - the commands
- `tests/cli.pl`, `io/ios.pl` - end-to-end tests and the 200 recorded runs
- `haskell/` - the Haskell version

## Proofs

Every output comes with `OUT.proof`, and nothing is written unless the
independent checker (`src/plop_proof.pl`) accepts it.
`plop2 proof-check SOURCE OUT OUT.proof` re-checks the proof from files. The
proof covers every clause:

- every source goal is **kept**, **dropped** or **consumed**;
- a goal is dropped only with a checked **totality certificate** (it always
  succeeds, once). A goal that may fail is kept;
- each position's program returns `c(Char)`, or `none` when the first
  answer's output is too short, so it never skips to a later answer;
- formulas are checked by exhaustive evaluation on their domain;
- input-character facts are checked by a watched symbolic run.

The rules are in [docs/proof_rules.md](docs/proof_rules.md).

## One program per character

```sh
plop2 chars examples/greet.pl double/2 3
```

```prolog
double__char1__alt([], R) :-
    R = none.
double__char1__alt([X|_], R) :-
    R = c(X).

double__char3__alt([], R) :-
    R = none.
double__char3__alt([_|Xs], R) :-
    double__char1__r(Xs, R).
```

Each position `K` also has `double__charK__r(In, R) :- once(double__charK__alt(In, R))`
and `double__charK(In, C) :- double__charK__r(In, c(C))`.

Given the program `double([X|Xs], [X,X|Ys]) :- double(Xs, Ys).`, plop2 builds
each position's program separately:

1. **Demand pushed back to its producer.** The demand "element K of V" goes
   to the goal that produces V.
2. **Calls become per-position programs.** A call `q(..., V)` becomes a call
   of q's own program for the needed position (`q__charJ`). q's other
   arguments are passed only if that program reads them; the rest are `_`.
3. **Builders unrolled for one position.** List and text builders are
   unrolled for that position only: `append/3`, `atom_concat/3`,
   `atomic_list_concat/2,3`, `atom_chars/2`, `atom_codes/2`,
   `number_codes/2` (a digit formula, `(N // 10^(D-K)) mod 10`), `reverse/2`,
   `maplist/3`, and literal lists such as `[H|T]` and `"abc"`.
4. **Only needed goals kept.** The goals kept are those that bind variables
   this character needs, plus guards and input matches that select clauses.
   Goals that only build other characters are dropped.
5. **Cuts removed first.** Cuts are turned into `if_commit/3` by detlog2
   before slicing, so the generated code is cut-free.

A recursion over the output becomes a chain of distinct programs (char3 calls
char1 on the tail), not one loop shared by all positions.

## Running positions 1..n on input character variables

```sh
plop2 run examples/greet.pl 'greet("bob", Out)' 12 -o greet_in.pl
```

```
  char 1: 'H'   (input characters none (constant or computed from non-text inputs))
  char 8: b   (input characters I1)
  char 9: o   (input characters I2)
  char 12: -   (no character 12 for inputs of this length)
characters 1..12: "Hello, bob!"
match: every position agrees with the original output
```

Inputs must be given as character lists. Each text input of length m is
replaced by m separate character variables `I1..Im`, and each position's
program is run on those variables.

- **Exactly one answer, input variables untouched.** The character is then a
  function of particular input characters and is written as data, for
  example `greet__char8__in([I1, _, _], I1).` This is what "unique" means
  here: one answer, and it binds no input character.
- **Positions that compute on character values.** If a position compares or
  transforms characters (upcasing, for example), or if the symbolic run gives
  several answers, that position is reported as computing on character
  values. It runs its sliced program on the actual characters.

The original algorithm's output (run with ordinary cut semantics) is
compared position by position.

## Formulas per position (mnns AlgebraPLOp)

```sh
plop2 formula examples/numbers.pl letter/2 3 --domain 0..20 --mnns ../mnns
char 1: code = linear(1, 97) at P = N - 0   [mnns AlgebraPLOp]
char 2: code = constant(45) at P = N - 0   [mnns AlgebraPLOp]
char 3: code = constant(120) at P = N - 0   [mnns AlgebraPLOp]
```

For each position whose program reads only the chosen integer input:

1. plop2 samples that position's character codes over the domain.
2. It calls `mnn_algebraplop:infer_sequence_formula/2` through SWI-Prolog.
   Without mnns, it uses a direct transcription of
   that predicate (same shapes, same order).
3. It re-checks the formula on every sample.
4. It emits a guarded closed form:

```prolog
letter__char1(N, C) :-
    (   integer(N), N >= 0, N =< 20
    ->  P is N - 0, Code is 1 * P + 97, char_code(C, Code)
    ;   letter__char1__sliced(N, C)
    ).
```

The formula is exact on the domain by exhaustion. Outside the domain, the
sliced program answers.

## Limits

- **Text built-ins in dropped goals** are assumed to receive values of their
  type. A type error would have aborted the original.
- **Text parts of a concatenation** that are built by non-user code (for
  example, digits from `number_codes/2` inside `append/3`) are read from
  their full value.
- **Recursion** over the output is sliced per position. Recursion that only
  builds other data is dropped when it is certified total (structural
  recursion on an input list); otherwise it is kept.
