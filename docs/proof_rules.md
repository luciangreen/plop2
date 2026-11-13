# plop2 proof rules

Every output of plop2 comes with a proof file `OUT.proof`. `Plop2.Proof`
checks the proof without using the slicer:
`plop2 proof-check SOURCE OUT OUT.proof`. Every command runs the checker
first and writes or runs nothing it rejects. The source is made cut-free by
detlog2's cut elimination, whose own proof rule (CUT) is in
[detlog2's docs](https://github.com/luciangreen/detlog2/blob/main/docs/proof_rules.md).

## What is proved

For a predicate p, an output argument and a position k, plop2 generates:

- `p__chark__alt(In…, R)`: one clause per source clause;
- `p__chark__r(In…, R) :- once(p__chark__alt(In…, R))`;
- `p__chark(In…, C) :- p__chark__r(In…, c(C))`.

**Claim.** For ground inputs, `p__chark__r` succeeds with `R = c(E)` exactly
when the original's first answer has an output whose element k is E. It
succeeds with `R = none` exactly when that output has fewer than k elements,
and it fails exactly when the original fails.

The proof is per clause. Each clause step records three things:

1. the source clause;
2. for every source goal, whether it is **kept**, **dropped** (with a
   totality certificate) or **consumed** (by the element expression);
3. the derivation of the element expression.

**First-answer lemma.** Suppose every dropped goal always succeeds, exactly
once, binding only variables that it binds first and that nothing kept reads.
Then the kept goals have the same first solution as in the original, and the
original clause's first answer extends it. A kept goal may fail, so keeping
it preserves clause selection; a dropped one never fails, so dropping it
changes nothing that the slice reads. This is why a goal without a
certificate is always kept.

**No later answers.** A clause whose output has no element k answers `none`
instead of failing. So `once/1` commits to the first clause that the original
would have used, and never to a later answer of the original. This was the
"dropped goals" bug: such a clause used to fail and fall through.

## Totality certificates (rule TOTAL)

Inputs are ground. A variable is ground after a goal if the goal's mode makes
it so (a fixed list of built-in modes). The checker re-derives groundness and
first occurrences itself. The certificates are:

| certificate | goal | condition |
| --- | --- | --- |
| `total(true)`, `total(output)` | `true`, `write/1`, `nl/0`, … | always succeed once |
| `total(fresh_unify)` | `X = T` | X first occurs here and not in T |
| `total(arith)` | `X is E` | X fresh; E ground; only `+ - *` |
| `total(text)` | `atom_codes(A, X)`, `atom_chars`, `char_code(X, Code)`, `atom_concat`, `atomic_list_concat`, … | inputs ground; output fresh |
| `total(append)`, `total(length)`, `total(reverse)` | `append(A, B, X)`, `length(L, X)`, `reverse(L, X)` | first input ground; output fresh |
| `total(pred(F/N, Mode))` | a user predicate | see below |

**User predicates.** `total(pred(F/N, Mode))` covers a user predicate called
with its Mode positions ground and its other positions fresh, distinct
variables. The predicate must have one of these shapes:

- **One clause.** Its input head arguments are distinct variables, and every
  body goal is total.
- **Two clauses that switch on an input list.** One clause has `[]` and the
  other `[H|T]` at that position, and the other input head arguments are
  distinct variables. Every body goal is total, and a recursive call must have
  T at the switch position: structural recursion, so it terminates on a
  proper list.

Head variables that occur only in output positions are fresh, because the
caller passes fresh variables there.

**Type assumption.** A text built-in in a dropped goal is assumed to receive
values of its type (for example, an atom for `atom_codes/2`). Such a goal
would raise an error in the original, not change an answer.

## Element rules

In each rule, S is the subject, k the position and R the result.

| rule | subject / producer | element expression |
| --- | --- | --- |
| el_head, el_tail | `[H|T]` | `R = c(H)` at k = 1, else element k−1 of T |
| el_const, el_none | atom, number, `[]`, or a variable that nothing binds | `R = c(Char)` or `R = none` |
| el_nth | any bound term (an input, or a variable a kept goal binds in full) | `plop2_nth_r(k, S, R)` |
| el_unify, el_alias | `V = T` (V first occurs here) / `V = W` | element k of T / of W |
| el_spec | `q(…, V, …)`, a user predicate | `q__chark__r(…, R, …)`: q's own program for position k. The arguments it reads are passed (and must be ground at the call); the others are fresh variables |
| el_chain, el_chain_const | `append/3`, `atom_concat/3`, `atomic_list_concat/2,3` | `plop2_chain(k, Parts, R)` over one closure per part (static elements, the value of a bound part, a dispatcher over a user predicate's per-position programs, or a nested chain); a position inside the static prefix is a constant |
| el_branch | `(C -> T ; E)`, `if_commit/3`, `(A ; B)` | the same branching, each branch sliced with its own kept, dropped and consumed goals |
| el_same_text, el_codes_of_text, el_text_of_codes | `atom_chars/2`, `atom_codes/2`, … | the element of the other argument, converted between character and code |
| el_number_codes, el_number_chars | `number_codes/2`, `number_chars/2`, `atom_number/2` | digit k by formula (`plop2_int_char/3`) |
| el_reverse | `reverse(L, V)` | element `len(L) − k + 1` of L |
| el_maplist | `maplist(F, L, V)` | F applied to element k of L |

**Side conditions the checker enforces.**

- The recorded producer is the goal where the subject first occurs.
- Every variable the expression reads is an input or is bound by a kept goal.
- No kept goal reads a variable of a consumed goal; otherwise that producer
  is kept in full and el_nth is used.
- Every fresh variable is new and is introduced once.

**Lemma for el_spec.** By induction on the derivation of q's first answer,
`q__chark__r` returns q's element k, or none, and fails exactly when q fails.
Consuming q is therefore sound when nothing else reads q's outputs (checked)
and the goals between q and the end of the clause do not depend on it.

**Helpers.** `plop2_nth_r`, `plop2_chain`, `plop2_static`, `plop2_value` and
`plop2_chain_c` are fixed, cut-free library predicates; the checker compares
them with its own copy. The lemma for `plop2_chain`: if part P has no element
K, it has some L < K elements (found by probing K−1, K−2, …), and element K of
the whole is element K−L of the remaining parts.

## Formula steps (rule FORMULA)

A formula clause `p__chark(N, C) :- ( integer(N), Lo =< N =< Hi -> formula ; p__chark__r(N, c(C)) )`
is checked by evaluation. For every N in Lo..Hi, the checker runs both the
formula and the sliced program and requires the same result. The formula is
therefore exact on the domain by exhaustion; outside it, the sliced program
answers. The formula itself comes from mnns AlgebraPLOp
(`infer_sequence_formula/2`), but its correctness does not depend on how it
was found.

## Input-character steps (rule SYMBOLIC)

A fact `p__chark__in([I1, _, I3], I3)` claims that, for every input of this
length, character k is input character 3. The checker re-runs
`p__chark__r` on unbound character variables in a *watched* run, in which any
type test or comparison on an input variable is an error. It requires:

- exactly one answer;
- input variables still distinct and unbound;
- the recorded value.

A watched run never inspects the characters, so its single answer holds for
every instantiation of them.
