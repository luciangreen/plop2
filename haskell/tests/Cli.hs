-- | End-to-end tests of the plop2 command line.  Run by Build.hs.
module Main (main) where

import Data.IORef
import Data.List (isInfixOf)
import System.Directory (findExecutable)
import System.Environment (lookupEnv)
import System.Exit
import System.Process (readProcessWithExitCode)

main :: IO ()
main = do
  fails <- newIORef (0 :: Int)
  let report name ok detail = if ok
        then putStrLn ("PASS " ++ name)
        else do
          putStrLn ("FAIL " ++ name)
          putStrLn (unlines (map ("    " ++) (lines detail)))
          modifyIORef fails (+ 1)
      runP exe args = do
        (_, o, e) <- readProcessWithExitCode exe args ""
        return (o ++ e)
      expectWith exe name want args = do
        o <- runP exe args
        report name (want `isInfixOf` o) o
      expect = expectWith "./build/hs/plop2"
      expectD2 = expectWith "./build/hs/detlog2"
      fileHas name want path = do
        s <- readFile path
        report name (want `isInfixOf` s) s
      fileLacks name bad path = do
        s <- readFile path
        report name (not (bad `isInfixOf` s)) s

  -- separate programs per position ----------------------------------------------
  _ <- runP "./build/hs/plop2" ["chars", "examples/greet.pl", "greet/2", "3", "-o", "build/greet3.pl"]
  fileHas "chars: char1 program" "greet__char1__alt(_, R)" "build/greet3.pl"
  fileHas "chars: char3 program" "greet__char3__alt(_, R)" "build/greet3.pl"
  fileLacks "chars: the output-building append is not kept" "append(" "build/greet3.pl"
  fileHas "chars: proof accepted" "proof accepted" "build/greet3.pl"
  expect "proof-check: accepted from files" "proof accepted"
    ["proof-check", "examples/greet.pl", "build/greet3.pl", "build/greet3.pl.proof"]
  greet3 <- readFile "build/greet3.pl"
  writeFile "build/greet3_bad.pl" (replaceFirst "c('H')" "c('J')" greet3)
  expect "proof-check: tampered code rejected" "proof rejected"
    ["proof-check", "examples/greet.pl", "build/greet3_bad.pl", "build/greet3.pl.proof"]
  _ <- runP "./build/hs/plop2" ["chars", "examples/greet.pl", "double/2", "3", "-o", "build/double3.pl"]
  fileHas "chars: double char3 calls char1's program on the tail" "double__char1__r(Xs, R)" "build/double3.pl"
  fileHas "chars: double char1 has no tail variable" "double__char1__alt([X|_], R)" "build/double3.pl"
  fileHas "chars: an empty output answers none" "double__char1__alt([], R)" "build/double3.pl"

  -- the dropped-goal bug: a clause whose output is too short answers none
  expect "run: first answer has no char 2, so none (no later answer)" "char 2: -"
    ["run", "examples/greet.pl", "short(x, Out)", "2"]
  expect "run: short matches" "match: every position agrees" ["run", "examples/greet.pl", "short(x, Out)", "2"]
  -- a goal that may fail is kept, not dropped
  expect "run: a guard on other data is kept" "match: every position agrees" ["run", "examples/greet.pl", "guarded(\"ab\", Out)", "3"]
  expect "run: guard failure is respected" "match: every position agrees" ["run", "examples/greet.pl", "guarded(\"abcdef\", Out)", "3"]

  -- run on input character variables -------------------------------------------
  expect "run: greet matches" "match: every position agrees" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "12"]
  expect "run: greet char 8 is input char 1" "char 8: b   (input characters I1)" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "12"]
  expect "run: greet char 1 is a constant" "char 1: 'H'   (input characters none" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "12"]
  expect "run: greet past the end" "char 12: -" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "12"]
  expect "run: proof accepted" "proof accepted" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "12"]
  expect "run: double" "char 3: b   (input characters I2)" ["run", "examples/greet.pl", "double(\"abc\", Out)", "6"]
  expect "run: double matches" "match: every position agrees" ["run", "examples/greet.pl", "double(\"abc\", Out)", "6"]
  expect "run: backwards" "char 1: c   (input characters I3)" ["run", "examples/greet.pl", "backwards(\"abc\", Out)", "3"]
  expect "run: shout computes on values" "computes on character values" ["run", "examples/greet.pl", "shout(\"abc\", Out)", "3"]
  expect "run: shout matches" "match: every position agrees" ["run", "examples/greet.pl", "shout(\"abc\", Out)", "3"]
  expect "run: tag (cut) matches" "match: every position agrees" ["run", "examples/greet.pl", "tag(\"ab\", Out)", "4"]
  expect "run: tag empty matches" "match: every position agrees" ["run", "examples/greet.pl", "tag([], Out)", "5"]
  expect "run: square matches" "match: every position agrees" ["run", "examples/numbers.pl", "square(12, Out)", "4"]
  expect "run: input must be given" "must be given" ["run", "examples/greet.pl", "greet(X, Out)", "3"]
  _ <- runP "./build/hs/plop2" ["run", "examples/greet.pl", "greet(\"bob\", Out)", "11", "-o", "build/greet_in.pl"]
  fileHas "run: per-position input-variable programs" "greet__char8__in([I1, _, _], I1)." "build/greet_in.pl"
  expect "proof-check: input-character facts re-checked symbolically" "proof accepted"
    ["proof-check", "examples/greet.pl", "build/greet_in.pl", "build/greet_in.pl.proof"]
  greetIn <- readFile "build/greet_in.pl"
  writeFile "build/greet_in_bad.pl" (replaceFirst "greet__char8__in([I1, _, _], I1)." "greet__char8__in([_, I2, _], I2)." greetIn)
  greetInProof <- readFile "build/greet_in.pl.proof"
  writeFile "build/greet_in_bad.pl.proof" (replaceFirst "input_chars_step(spec(greet/2, 1, 8), greet__char8__in([" "input_chars_step(spec(greet/2, 1, 8), greet__char8__in([_, " greetInProof)
  expect "proof-check: a wrong input-character fact is rejected" "proof rejected"
    ["proof-check", "examples/greet.pl", "build/greet_in_bad.pl", "build/greet_in.pl.proof"]

  -- formulas through mnns AlgebraPLOp ----------------------------------------------
  expect "formula: linear code" "char 1: code = linear(1, 97)" ["formula", "examples/numbers.pl", "letter/2", "3", "--domain", "0..20"]
  expect "formula: constant" "char 3: code = constant(120)" ["formula", "examples/numbers.pl", "letter/2", "3", "--domain", "0..20"]
  expect "formula: none for first digit of a square" "char 1: no formula" ["formula", "examples/numbers.pl", "square/2", "1", "--domain", "1..12"]
  swipl <- findExecutable "swipl"
  mnns <- lookupEnv "MNNS_DIR"
  case (swipl, mnns) of
    (Just _, Just dir) ->
      expect "formula: found by mnns" "[mnns AlgebraPLOp]" ["formula", "examples/numbers.pl", "letter/2", "1", "--domain", "0..20", "--mnns", dir]
    _ -> putStrLn "SKIP mnns formula (swipl or MNNS_DIR missing)"
  _ <- runP "./build/hs/plop2" ["formula", "examples/numbers.pl", "letter/2", "3", "--domain", "0..20", "-o", "build/letter.pl"]
  fileHas "formula: guarded formula clause" "integer(N)" "build/letter.pl"
  fileHas "formula: sliced program outside the domain" "letter__char1__r(N, c(C))" "build/letter.pl"
  fileHas "formula: char 2 drops char 1's computation with certificates" "total(arith)" "build/letter.pl.proof"
  expect "proof-check: formulas re-checked by evaluation" "proof accepted"
    ["proof-check", "examples/numbers.pl", "build/letter.pl", "build/letter.pl.proof"]
  letterProof <- readFile "build/letter.pl.proof"
  writeFile "build/letter_bad.proof" (replaceFirst "total(arith)" "total(text)" letterProof)
  expect "proof-check: a wrong certificate is rejected" "proof rejected"
    ["proof-check", "examples/numbers.pl", "build/letter.pl", "build/letter_bad.proof"]
  letter <- readFile "build/letter.pl"
  writeFile "build/letter_bad.pl" (replaceFirst "1 * P + 97" "1 * P + 98" letter)
  writeFile "build/letter_bad2.proof" (replaceFirst "1 * P + 97" "1 * P + 98" letterProof)
  expect "proof-check: a wrong formula is rejected" "proof rejected"
    ["proof-check", "examples/numbers.pl", "build/letter_bad.pl", "build/letter_bad2.proof"]

  -- generated files run on detlog2 (cut-free)
  expectD2 "detlog2 runs letter formula" "C = d." ["run", "build/letter.pl", "letter__char1(3, C)"]
  expectD2 "detlog2 runs letter outside the domain" "C = z." ["run", "build/letter.pl", "letter__char1(25, C)"]
  expectD2 "detlog2 runs greet char 9" "C = o." ["run", "build/greet_in.pl", "greet__char9(\"bob\", C)"]

  n <- readIORef fails
  putStrLn ""
  if n == 0 then putStrLn "all CLI tests passed" else do
    putStrLn (show n ++ " CLI test(s) failed")
    exitWith (ExitFailure 1)

replaceFirst :: String -> String -> String -> String
replaceFirst old new = go
  where
    go [] = []
    go s@(c : cs)
      | take (length old) s == old = new ++ drop (length old) s
      | otherwise = c : go cs
