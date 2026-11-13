-- | 200 inputs and the outputs they give, from real runs of plop2.
--
--   runghc Build.hs ios        runs the 200 inputs and writes io/ios.txt
--   runghc Build.hs check-ios  runs them again and fails if any output changed
--
-- The inputs are made the same way every time (see 'cases').  Each output is
-- everything the command printed, with its exit code when that is not 0.
module Main (main) where

import Data.Char (isAlphaNum)
import Data.List (intercalate)
import System.Environment (getArgs, getEnvironment)
import System.Exit
import System.Process

title :: String
title = "plop2"

binary :: FilePath
binary = "./build/hs/plop2"

-- | Choose element i (from the case number k and a salt) of a list.
pick :: Int -> Int -> [a] -> a
pick k salt xs = xs !! ((k * (2 * salt + 1) + salt * 7) `mod` length xs)

-- | A list of length n from a pool, starting at a place set by k.
pickN :: Int -> Int -> Int -> [a] -> [a]
pickN k salt n xs = take n (drop ((k * (salt + 3)) `mod` length xs) (cycle xs))

showList' :: [Int] -> String
showList' xs = "[" ++ intercalate "," (map show xs) ++ "]"

pool :: [Int]
pool = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

-- | Input texts, given as character lists.
texts :: [String]
texts = ["bob", "al", "zoe", "kim", "ed", "abc", "x", "lucian", "mnn", "ok", "prolog", "", "aa", "abcdef"]

str :: Int -> Int -> String
str k salt = show (pick k salt texts)

-- | The 200 inputs: (command arguments).
cases :: [[String]]
cases = [ caseFor k | k <- [1 .. 200] ]

caseFor :: Int -> [String]
caseFor k = case k `mod` 10 of
  0 -> ["run", "examples/greet.pl", "greet(" ++ str k 1 ++ ", Out)", show (1 + k `mod` 12)]
  1 -> ["run", "examples/greet.pl", "double(" ++ str k 2 ++ ", Out)", show (1 + k `mod` 8)]
  2 -> ["run", "examples/greet.pl", "backwards(" ++ str k 3 ++ ", Out)", show (1 + k `mod` 6)]
  3 -> ["run", "examples/greet.pl", "tag(" ++ str k 4 ++ ", Out)", show (1 + k `mod` 9)]
  4 -> ["run", "examples/greet.pl", "guarded(" ++ str k 5 ++ ", Out)", show (1 + k `mod` 9)]
  5 -> ["run", "examples/numbers.pl", "square(" ++ show (k `mod` 40) ++ ", Out)", show (1 + k `mod` 5)]
  6 -> ["run", "examples/greet.pl", pick k 6 ["short(x, Out)", "shout(" ++ str k 7 ++ ", Out)"], show (1 + k `mod` 4)]
  7 -> ["run", "examples/numbers.pl", "letter(" ++ show (k `mod` 26) ++ ", Out)", show (1 + k `mod` 4)]
  8 -> ["formula", "examples/numbers.pl", "letter/2", show (1 + k `mod` 3)
       , "--domain", show (k `mod` 5) ++ ".." ++ show (k `mod` 5 + 5 + k `mod` 7)]
  _ -> ["chars", "examples/greet.pl", pick k 8 ["greet/2", "double/2", "tag/2", "guarded/2", "short/2"], show (1 + k `mod` 3)]

quoteArg :: String -> String
quoteArg a
  | all (\c -> isAlphaNum c || c `elem` "/._-") a && not (null a) = a
  | otherwise = "'" ++ concatMap (\c -> if c == '\'' then "'\\''" else [c]) a ++ "'"

runCase :: [(String, String)] -> [String] -> IO String
runCase env args = do
  (code, out, err) <- readCreateProcessWithExitCode ((proc binary args) { env = Just env }) ""
  let text = trimEnd (out ++ err)
      codeLine = case code of
        ExitSuccess -> ""
        ExitFailure n -> "\n(exit code " ++ show n ++ ")"
  return (text ++ codeLine)
  where
    trimEnd = reverse . dropWhile (`elem` " \n") . reverse

render :: [([String], String)] -> String
render results = unlines $
  (title ++ ": 200 inputs and outputs, from real runs (runghc Build.hs ios writes this file; "
     ++ "runghc Build.hs check-ios checks it).")
  : concat [ [ "", show i ++ ". " ++ unwords (title : map quoteArg args) ]
             ++ case lines out of
                  [] -> ["   => (no output)"]
                  (l : ls) -> ("   => " ++ l) : map ("      " ++) ls
           | (i, (args, out)) <- zip [1 :: Int ..] results ]

main :: IO ()
main = do
  mode <- getArgs
  env0 <- getEnvironment
  -- the same runs everywhere: no optional tools from the environment
  let env = filter ((`notElem` ["MNNS_DIR"]) . fst) env0
  outs <- mapM (runCase env) cases
  let text = render (zip cases outs)
  case mode of
    ["make"] -> writeFile "haskell/io/ios.txt" text >> putStrLn "wrote haskell/io/ios.txt (200 inputs and outputs)"
    ["check"] -> do
      old <- readFile "haskell/io/ios.txt"
      if length old == length text && old == text
        then putStrLn "All 200 inputs give the outputs in io/ios.txt."
        else do
          let diffs = [ (n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines old) (lines text), a /= b ]
          mapM_ (\(n, a, b) -> putStrLn ("line " ++ show n ++ ":\n  recorded: " ++ a ++ "\n  now:      " ++ b)) (take 20 diffs)
          putStrLn "Outputs differ from io/ios.txt. If the change is meant, run runghc Build.hs ios and commit io/ios.txt."
          exitWith (ExitFailure 1)
    _ -> putStrLn "usage: ios make | ios check" >> exitWith (ExitFailure 2)
