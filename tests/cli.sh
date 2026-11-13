#!/usr/bin/env bash
# End-to-end tests of the plop2 command line.
set -uo pipefail
cd "$(dirname "$0")/.."
P=./build/plop2
D2=${DETLOG2_BIN:-}
fails=0
pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; echo "$2" | sed 's/^/    /'; fails=$((fails + 1)); }
expect() {
  local name=$1 want=$2; shift 2
  local out
  out=$("$@" 2>&1)
  if grep -qF -- "$want" <<<"$out"; then pass "$name"; else fail "$name" "$out"; fi
}
expect_not() {
  local name=$1 bad=$2; shift 2
  local out
  out=$("$@" 2>&1)
  if grep -qF -- "$bad" <<<"$out"; then fail "$name" "$out"; else pass "$name"; fi
}

# --- separate programs per position ------------------------------------------
$P chars examples/greet.pl greet/2 3 -o build/greet3.pl >/dev/null 2>&1
expect "chars: char1 program" "greet__char1(_, C)" cat build/greet3.pl
expect "chars: char3 program" "greet__char3(_, C)" cat build/greet3.pl
expect_not "chars: no whole-output append kept" "append(" cat build/greet3.pl
$P chars examples/greet.pl double/2 3 -o build/double3.pl >/dev/null 2>&1
expect "chars: double char3 calls char1 on the tail" "double__char1(Xs, C)" cat build/double3.pl
expect "chars: double char1 has no tail variable" "double__char1([X|_], C)" cat build/double3.pl

# --- run on input character variables ----------------------------------------
expect "run: greet matches" "match: every position agrees" $P run examples/greet.pl 'greet("bob", Out)' 12
expect "run: greet char 8 is input char 1" "char 8: b   (input characters I1)" $P run examples/greet.pl 'greet("bob", Out)' 12
expect "run: greet char 1 is a constant" "char 1: 'H'   (input characters none" $P run examples/greet.pl 'greet("bob", Out)' 12
expect "run: greet past the end" "char 12: -" $P run examples/greet.pl 'greet("bob", Out)' 12
expect "run: double" "char 3: b   (input characters I2)" $P run examples/greet.pl 'double("abc", Out)' 6
expect "run: double matches" "match: every position agrees" $P run examples/greet.pl 'double("abc", Out)' 6
expect "run: backwards" "char 1: c   (input characters I3)" $P run examples/greet.pl 'backwards("abc", Out)' 3
expect "run: shout computes on values" "computes on character values" $P run examples/greet.pl 'shout("abc", Out)' 3
expect "run: shout matches" "match: every position agrees" $P run examples/greet.pl 'shout("abc", Out)' 3
expect "run: tag (cut) matches" "match: every position agrees" $P run examples/greet.pl 'tag("ab", Out)' 4
expect "run: tag empty matches" "match: every position agrees" $P run examples/greet.pl 'tag([], Out)' 5
expect "run: square matches" "match: every position agrees" $P run examples/numbers.pl 'square(12, Out)' 4
expect "run: input must be given" "must be given" $P run examples/greet.pl 'greet(X, Out)' 3
$P run examples/greet.pl 'greet("bob", Out)' 11 -o build/greet_in.pl >/dev/null 2>&1
expect "run: writes per-position input-variable programs" "greet__char8__in([I1, _, _], I1)." cat build/greet_in.pl

# --- formulas through mnns AlgebraPLOp ------------------------------------------
expect "formula: linear code" "char 1: code = linear(1, 97)" $P formula examples/numbers.pl letter/2 3 --domain 0..20
expect "formula: constant" "char 3: code = constant(120)" $P formula examples/numbers.pl letter/2 3 --domain 0..20
expect "formula: none for first digit of a square" "char 1: no formula" $P formula examples/numbers.pl square/2 1 --domain 1..12
if command -v swipl >/dev/null 2>&1 && [ -n "${MNNS_DIR:-}" ]; then
  expect "formula: found by mnns" "[mnns AlgebraPLOp]" $P formula examples/numbers.pl letter/2 1 --domain 0..20 --mnns "$MNNS_DIR"
else
  echo "SKIP mnns formula (swipl or MNNS_DIR missing)"
fi
$P formula examples/numbers.pl letter/2 3 --domain 0..20 -o build/letter.pl >/dev/null 2>&1
expect "formula: guarded formula clause" "integer(N)" cat build/letter.pl
expect "formula: sliced fallback kept" "letter__char1__sliced(" cat build/letter.pl

# generated files run on detlog2 (cut-free)
if [ -n "${DETLOG2_DIR:-}" ] && [ -x "$DETLOG2_DIR/build/detlog2" ]; then
  expect "detlog2 runs letter formula" "C = d." "$DETLOG2_DIR/build/detlog2" run build/letter.pl 'letter__char1(3, C)'
  expect "detlog2 runs letter outside domain" "C = z." "$DETLOG2_DIR/build/detlog2" run build/letter.pl 'letter__char1(25, C)'
  expect "detlog2 runs greet char 9" "C = o." "$DETLOG2_DIR/build/detlog2" run build/greet_in.pl 'greet__char9("bob", C)'
fi

echo
if [ "$fails" -eq 0 ]; then echo "all CLI tests passed"; else echo "$fails CLI test(s) failed"; exit 1; fi
