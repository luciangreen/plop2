-- | Closed forms for one output position, using mnns's AlgebraPLOp.
--
-- For a position k and an integer input N over a domain Lo..Hi, plop2
-- samples the character codes of position k and asks
-- @mnn_algebraplop:infer_sequence_formula/2@ (github.com/luciangreen/mnns,
-- prolog/algebraplop/algebraplop.pl) for a formula.  When SWI-Prolog or mnns
-- is not available, the same inference is run by a direct Haskell
-- transcription of that predicate (same shapes, same order, same held-out
-- check).  Either way the formula is then re-checked on every sample before
-- it is used, and the generated code guards it with the sampled domain, so
-- it is exact by exhaustion on Lo..Hi and the sliced program answers outside.
module Plop2.Formula
  ( Formula(..)
  , inferNative
  , inferWithMnns
  , evalFormula
  , formulaExpr
  , formulaTerm
  , showFormula
  ) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)
import Detlog2.Parser (parseTermString)
import Detlog2.Pretty (showTermQ)
import Detlog2.Term

data Formula
  = Constant Integer
  | Linear Integer Integer                 -- slope, intercept
  | Quadratic Integer Integer Integer      -- intercept, first difference, second difference
  | Exponential Integer Integer            -- initial, base
  | Polynomial [Integer]                   -- Newton forward-difference coefficients
  deriving (Eq, Show)

showFormula :: Formula -> String
showFormula = showTermQ . formulaTerm

-- | The formula as mnns writes it (without verified_on/1).
formulaTerm :: Formula -> Term
formulaTerm f = case f of
  Constant v -> Comp "constant" [Int v]
  Linear s i -> Comp "linear" [Int s, Int i]
  Quadratic i d1 d2 -> Comp "quadratic" [Int i, Int d1, Int d2]
  Exponential i b -> Comp "exponential" [Int i, Int b]
  Polynomial cs -> Comp "polynomial" [mkList (map Int cs) (Atom "[]")]

evalFormula :: Formula -> Integer -> Integer
evalFormula f p = case f of
  Constant v -> v
  Linear s i -> s * p + i
  Quadratic i d1 d2 -> i + d1 * p + d2 * (p * (p - 1) `div` 2)
  Exponential i b -> i * b ^ p
  Polynomial cs -> sum [ c * binom p j | (j, c) <- zip [0 ..] cs ]

binom :: Integer -> Integer -> Integer
binom n j
  | j > n = 0
  | otherwise = product [n - j + 1 .. n] `div` product [1 .. j]

-- | An arithmetic expression for is/2 in the position variable P.
formulaExpr :: Formula -> Term -> Term
formulaExpr f p = case f of
  Constant v -> Int v
  Linear s i -> plus (times (Int s) p) (Int i)
  Quadratic i d1 d2 ->
    plus (plus (Int i) (times (Int d1) p))
         (times (Int d2) (Comp "//" [times p (Comp "-" [p, Int 1]), Int 2]))
  Exponential i b -> times (Int i) (Comp "^" [Int b, p])
  Polynomial cs -> foldl1 plus [ times (Int c) (binomExpr j) | (j, c) <- zip [0 ..] cs ]
  where
    plus a b = Comp "+" [a, b]
    times a b = Comp "*" [a, b]
    -- C(P, j) = P (P-1) ... (P-j+1) // j!
    binomExpr :: Integer -> Term
    binomExpr 0 = Int 1
    binomExpr j = Comp "//" [ foldl1 times [ Comp "-" [p, Int i] | i <- [0 .. j - 1] ]
                            , Int (product [1 .. j]) ]

-- | Direct transcription of mnn_algebraplop:infer_sequence_formula/2.
inferNative :: [Integer] -> Maybe Formula
inferNative xs
  | length xs < 3 = Nothing
  | all (== head xs) xs = Just (Constant (head xs))
  | otherwise = firstJust [linear, quadratic, geometric, polynomial]
  where
    firstJust [] = Nothing
    firstJust (f : fs) = maybe (firstJust fs) Just (f ())
    linear () = case xs of
      (i : s2 : _) -> let s = s2 - i in check (Linear s i)
      _ -> Nothing
    quadratic () = case xs of
      (i : s2 : s3 : _ : _) -> let d1 = s2 - i
                                   d2 = (s3 - s2) - d1
                               in check (Quadratic i d1 d2)
      _ -> Nothing
    geometric () = case xs of
      (i : s2 : _) | i /= 0 && s2 `mod` i == 0 -> check (Exponential i (s2 `div` i))
      _ -> Nothing
    polynomial () = firstJust [ \() -> polyOf d | d <- [3 .. toInteger (length xs) - 2] ]
    polyOf d =
      let prefix = take (fromIntegral d + 1) xs
          cs = forward prefix
      in if last cs /= 0 then check (Polynomial cs) else Nothing
    forward [v] = [v]
    forward vs@(v : _) = v : forward (zipWith (-) (tail vs) vs)
    forward [] = []
    check f = if and [ evalFormula f p == x | (p, x) <- zip [0 ..] xs ] then Just f else Nothing

-- | Ask mnns (through SWI-Prolog).  Left explains why mnns was not used.
inferWithMnns :: FilePath -> [Integer] -> IO (Either String (Maybe Formula))
inferWithMnns dir xs = do
  let file = dir ++ "/prolog/algebraplop/algebraplop.pl"
      goal = "use_module('" ++ file ++ "'), mnn_algebraplop:infer_sequence_formula(["
             ++ intercalate "," (map show xs) ++ "], F), writeq(F), nl"
  r <- try (readProcessWithExitCode "swipl" ["-q", "-g", goal, "-t", "halt"] "")
         :: IO (Either IOException (ExitCode, String, String))
  return $ case r of
    Left e -> Left ("swipl not available: " ++ show e)
    Right (ExitSuccess, out, _) -> case parseTermString out of
      Right (t, _, _) -> Right (fromMnns t)
      Left e -> Left ("could not read mnns's answer " ++ show out ++ ": " ++ e)
    Right (_, out, err) -> Left ("mnns failed: " ++ out ++ err)

fromMnns :: Term -> Maybe Formula
fromMnns t = case t of
  Comp "formula" [shape, _] -> case shape of
    Comp "constant" [Int v] -> Just (Constant v)
    Comp "linear" [Int s, Int i] -> Just (Linear s i)
    Comp "quadratic" [Int i, Int a, Int b] -> Just (Quadratic i a b)
    Comp "exponential" [Int i, Int b] -> Just (Exponential i b)
    Comp "polynomial" [l] -> Polynomial <$> ints l
    _ -> Nothing
  _ -> Nothing
  where
    ints (Atom "[]") = Just []
    ints (Comp "." [Int i, rest]) = (i :) <$> ints rest
    ints _ = Nothing
