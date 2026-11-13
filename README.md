# plop2

plop2 writes **one separate program per output character** of an algorithm.
Each program, `p__charK`, computes only character K: nothing for characters
1..K-1 or K+1..n, and no variables for the other data. Given n, plop2 runs
these n finite programs and checks them against the original algorithm.

It is built on [detlog2](https://github.com/luciangreen/detlog2): the reader,
the cut-free interpreter, and cut elimination. Closed forms come from
[mnns](https://github.com/luciangreen/mnns)'s AlgebraPLOp.

## Build

```sh
git clone https://github.com/luciangreen/detlog2 ../detlog2   # or set DETLOG2_DIR
./scripts/ci.sh            # builds build/plop2 and runs the tests
```

## One program per character

```sh
plop2 chars examples/greet.pl double/2 3
```

```prolog
double__char1([X|_], C) :-
    C = X.

double__char2([X|_], C) :-
    C = X.

double__char3([_|Xs], C) :-
    double__char1(Xs, C).
```

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
   Without SWI-Prolog or mnns, it uses a direct Haskell transcription of
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

## Assumption

A dropped goal only built data for other characters, and is assumed to have
succeeded. `plop2 run` checks every position against the original output, so
any program where this does not hold shows up as a mismatch.
