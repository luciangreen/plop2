-- | plop2 command line.
module Main (main) where

import Control.Monad (forM, forM_, unless)
import Data.Char (ord)
import Data.List (intercalate, isPrefixOf, sortOn)
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import System.Environment (getArgs, lookupEnv)
import System.Exit
import System.IO

import Detlog2.Builtins (Ev(..))
import Detlog2.CutElim (eliminateCuts, showCutEvent)
import Detlog2.Interp
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference
import Detlog2.Term
import Plop2.Formula
import Plop2.Slice

usage :: String
usage = unlines
  [ "plop2 - one separate, minimal program per output character"
  , ""
  , "  plop2 chars FILE NAME/ARITY N [--out-arg I] [-o OUT]"
  , "        write NAME__char1 .. NAME__charN, each computing only its character"
  , "  plop2 run FILE GOAL N [--out-arg I] [-o OUT]"
  , "        give the inputs as character lists (\"...\"); each position's program is run"
  , "        on input character variables I1..Im, then on the input; compares with the"
  , "        original algorithm's output"
  , "  plop2 formula FILE NAME/ARITY N --domain LO..HI [--domain-arg I] [--mnns DIR] [-o OUT]"
  , "        closed forms per position for an integer input, found with mnns AlgebraPLOp"
  , ""
  , "Argument positions are 1-based; the output argument defaults to the last."
  ]

data Flags = Flags
  { fOutArg :: Maybe Int
  , fOutFile :: Maybe FilePath
  , fDomain :: Maybe (Integer, Integer)
  , fDomainArg :: Int
  , fMnns :: Maybe FilePath
  , fPos :: [String]
  }

parseFlags :: [String] -> Either String Flags
parseFlags = go (Flags Nothing Nothing Nothing 1 Nothing [])
  where
    go f [] = Right f { fPos = reverse (fPos f) }
    go f ("--out-arg" : i : r) = go f { fOutArg = Just (read i) } r
    go f ("-o" : o : r) = go f { fOutFile = Just o } r
    go f ("--domain" : d : r) = case break (== '.') d of
      (lo, '.' : '.' : hi) -> go f { fDomain = Just (read lo, read hi) } r
      _ -> Left "--domain expects LO..HI"
    go f ("--domain-arg" : i : r) = go f { fDomainArg = read i } r
    go f ("--mnns" : d : r) = go f { fMnns = Just d } r
    go _ (x : _) | "--" `isPrefixOf` x = Left ("unknown option " ++ x)
    go f (x : r) = go f { fPos = x : fPos f } r

die' :: String -> IO a
die' m = hPutStrLn stderr ("plop2: " ++ m) >> exitWith (ExitFailure 1)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  case args of
    [] -> putStr usage
    ("help" : _) -> putStr usage
    (cmd : rest) -> either die' (dispatch cmd) (parseFlags rest)

loadCutFree :: FilePath -> IO (Program, [String])
loadCutFree path = do
  src <- readFile path
  p <- either (\e -> die' (path ++ ": " ++ e)) return (parseProgram src)
  case eliminateCuts p of
    Left bad -> die' ("cuts that cannot be converted:\n  " ++ intercalate "\n  " (map showCutEvent bad))
    Right (p', evs) -> return (p', map showCutEvent evs)

parseKey :: String -> IO PredKey
parseKey s = case break (== '/') s of
  (f, '/' : n) | not (null f) -> return (f, read n)
  _ -> die' ("expected NAME/ARITY, got " ++ s)

helpers :: Program
helpers = either (\e -> error ("helpers: " ++ e)) id (parseProgram helperSource)

dispatch :: String -> Flags -> IO ()
dispatch cmd fl = case (cmd, fPos fl) of
  ("chars", [file, keyS, nS]) -> do
    (p, evs) <- loadCutFree file
    key <- parseKey keyS
    let n = read nS
        j = maybe (snd key - 1) (subtract 1) (fOutArg fl)
        sr = slicePositions p key j n
    writeOut fl (header file evs sr) (generated p sr key j n Nothing)
  ("run", [file, goalS, nS]) -> runCmd fl file goalS (read nS)
  ("formula", [file, keyS, nS]) -> formulaCmd fl file keyS (read nS)
  _ -> die' ("bad arguments\n" ++ usage)

header :: FilePath -> [String] -> SliceResult -> String
header file evs sr = unlines $
  [ "% plop2: one program per output character, generated from " ++ file
  , "% Each NAME__charK computes only character K: it keeps only the goals that"
  , "% bind what character K needs, and has no variables for the other characters."
  , "% The code is cut-free (runs on detlog2 and SWI-Prolog)."
  ] ++ [ "% " ++ e | e <- evs ] ++ [ "% note: " ++ x | x <- Set.toList (Set.fromList (srNotes sr)) ]

-- | The specialised programs in position order, then helpers and the
-- original predicates that kept goals still call.
generated :: Program -> SliceResult -> PredKey -> Int -> Int -> Maybe [Clause] -> Program
generated p sr key j n extra =
  let roots = [ Spec key j k | k <- [1 .. n] ]
      others = [ sp | sp <- M.keys (srClauses sr), sp `notElem` roots ]
      ordered = roots ++ sortOn (\(Spec (f, a) o k) -> (f, a, o, k)) others
      specCls = concat [ M.findWithDefault [] sp (srClauses sr) | sp <- ordered ]
      used = reachableSource p (specCls ++ maybe [] id extra)
      cls = maybe [] id extra ++ specCls ++ concatMap snd (programClauses helpers)
            ++ concat [ cs | (k', cs) <- programClauses p, Set.member k' used ]
  in programFromClauses cls

reachableSource :: Program -> [Clause] -> Set.Set PredKey
reachableSource p cls = go Set.empty (concatMap (calls . clBody) cls)
  where
    go seen [] = seen
    go seen (k : ks)
      | Set.member k seen || not (M.member k (progPreds p)) = go seen ks
      | otherwise = go (Set.insert k seen)
                       (ks ++ concatMap (calls . clBody) (M.findWithDefault [] k (progPreds p)))
    calls t = case t of
      Comp op as | op `elem` [",", ";", "->", "if_commit", "\\+", "findall", "forall", "once"] ->
        concatMap calls as
      _ -> maybe [] (: []) (goalKey t)

writeOut :: Flags -> String -> Program -> IO ()
writeOut fl hdr prog = do
  let text = hdr ++ "\n" ++ showProgram prog
  case fOutFile fl of
    Nothing -> putStr text
    Just o -> writeFile o text >> hPutStrLn stderr ("wrote " ++ o)

runProgram :: Program -> Program
runProgram = withPrelude

-- | First answer of a goal on the cutless interpreter, with the value of a term.
firstValue :: Program -> Term -> Int -> Term -> Either String (Maybe Term)
firstValue prog goal nv t = scan (runGoal defaultOptions prog goal nv)
  where
    scan [] = Right Nothing
    scan (Out _ : r) = scan r
    scan (Err e : _) = Left e
    scan (Ans s : _) = Right (Just (resolve s t))

-- ---------------------------------------------------------------------------
-- run: input character variables

runCmd :: Flags -> FilePath -> String -> Int -> IO ()
runCmd fl file goalS n = do
  (p, evs) <- loadCutFree file
  (goal, _, nv) <- either (\e -> die' ("goal: " ++ e)) return (parseQuery goalS)
  key <- maybe (die' "goal is not callable") return (goalKey goal)
  let args = goalArgs goal
      j = maybe (length args - 1) (subtract 1) (fOutArg fl)
      inputs = [ (i, a) | (i, a) <- zip [0 ..] args, i /= j ]
  -- inputs must be character lists (or other ground values that are not text)
  forM_ inputs $ \(i, a) -> unless (null (termVarsOrdered a)) $
    die' ("input argument " ++ show (i + 1) ++ " must be given (as a character list \"...\")")
  let textInputs = [ (i, cs) | (i, a) <- inputs, Just cs <- [charsOf a] ]
      sr = slicePositions p key j n
      base = generated p sr key j n Nothing
      prog = runProgram base
      -- input character variables I<arg>_<pos>
      symArg i a = case lookup i textInputs of
        Just cs -> mkList [ Var (1000 * (i + 1) + q) ("I" ++ suffix i q) | q <- [1 .. length cs] ] (Atom "[]")
        Nothing -> a
      suffix i q = if length textInputs == 1 then show q else show (i + 1) ++ "_" ++ show q
      symArgs = [ if i == j then Atom "$out" else symArg i a | (i, a) <- zip [0 ..] args ]
      inputName v = head ([ n' | a <- symArgs, Var w n' <- termVarsOrdered a, w == v ] ++ ["I"])
      inputVarIds = IS.fromList [ v | a <- symArgs, Var v _ <- termVarsOrdered a ]
  -- reference output of the original algorithm
  let refStream = refRun defaultOptions (withPrelude p) goal nv
      refOut = case [ s | Ans s <- refStream ] of
        (s : _) -> Just (resolve s (args !! j))
        [] -> Nothing
      refElems = refOut >>= elementsOf
  results <- forM [1 .. n] $ \k -> do
    let sp = Spec key j k
        name = specName sp
        cVar = Var 900000 "C"
        symGoal = Comp name [ if i == j then cVar else a | (i, a) <- zip [0 ..] symArgs ]
        concGoal = Comp name [ if i == j then cVar else a | (i, a) <- zip [0 ..] args ]
        symStream = take 200 (runGoal defaultOptions { optMaxDepth = 20000 } prog symGoal 900001)
        symAnswers = [ s | Ans s <- symStream ]
        symErr = [ e | Err e <- symStream ]
        concrete = firstValue prog concGoal 900001 cVar
    case (symErr, symAnswers) of
      ([], [s]) | inputsUntouched s inputVarIds -> do
        -- a pure function of the input characters: emit it as data.  The
        -- run may have aliased an input variable to a fresh one; map back.
        let back = M.fromList [ (w, Var v n') | v <- IS.toList inputVarIds
                                             , Var w _ <- [walk s (Var v "")]
                                             , let n' = inputName v ]
            unalias t = case t of
              Var w _ -> M.findWithDefault t w back
              Comp f as -> Comp f (map unalias as)
              _ -> t
            val = unalias (resolve s cVar)
            headArgs = [ if i == j then val else a | (i, a) <- zip [0 ..] symArgs ]
            cl = Clause (Comp (name ++ "__in") headArgs) (Atom "true") 900001
            actual = substituteInputs textInputs val
        return (k, actual, Just cl, "input characters " ++ depends val)
      ([], []) -> return (k, Nothing, Nothing, "no character " ++ show k ++ " for inputs of this length")
      _ -> do
        let why = case (symErr, symAnswers) of
              (e : _, _) -> "computes on character values (" ++ takeWhile (/= '\n') e ++ ")"
              (_, _ : _ : _) -> "not unique on input character variables (several answers)"
              _ -> "depends on character values"
            headArgs = [ if i == j then cVar else a | (i, a) <- zip [0 ..] symArgs ]
            cl = Clause (Comp (name ++ "__in") headArgs) (Comp name headArgs) 900001
        case concrete of
          Left e -> return (k, Nothing, Just cl, why ++ "; error: " ++ e)
          Right v -> return (k, v, Just cl, why)
  let produced = [ v | (_, Just v, _, _) <- results ]
      extra = [ c | (_, _, Just c, _) <- results ]
      prefix = takeWhile (/= Nothing) [ v | (_, v, _, _) <- results ]
  putStrLn ("goal: " ++ goalS)
  forM_ results $ \(k, v, _, how) ->
    putStrLn ("  char " ++ show k ++ ": " ++ maybe "-" showTermQ v ++ "   (" ++ how ++ ")")
  let shown = concatMap (maybe "" showChar' ) prefix
  putStrLn ("characters 1.." ++ show n ++ ": " ++ show shown)
  case refElems of
    Nothing -> putStrLn "original algorithm: no output (it failed or raised an error)"
    Just es -> do
      let want = take n es
          got = take (length want) (map Just produced ++ repeat Nothing)
          okLen = length prefix == length want
          ok = okLen && and (zipWith (\a b -> b == Just a) want got)
      putStrLn ("original algorithm, first " ++ show n ++ ": " ++ show (concatMap showChar' want))
      if ok then putStrLn "match: every position agrees with the original output"
            else putStrLn "MISMATCH with the original output" >> exitWith (ExitFailure 1)
  let hdr = header file evs sr
            ++ "% NAME__charK__in: the program for character K over input character variables.\n"
  case fOutFile fl of
    Nothing -> return ()
    Just _ -> writeOut fl hdr (generated p sr key j n (Just extra))
  where
    -- every input character variable is still an unbound variable, and no
    -- two of them were made equal
    inputsUntouched s ids = all (\v -> case walk s (Var v "") of
                                         Var _ _ -> True
                                         _ -> False) (IS.toList ids)
                            && distinctUnbound s ids
    distinctUnbound s ids =
      let ws = [ w | v <- IS.toList ids, Var w _ <- [walk s (Var v "")] ]
      in length ws == length (Set.fromList ws)
    depends val = case [ n' | Var _ n' <- termVarsOrdered val ] of
      [] -> "none (constant or computed from non-text inputs)"
      ns -> intercalate ", " ns

charsOf :: Term -> Maybe [Term]
charsOf t = case t of
  Atom "[]" -> Just []
  Comp "." [h@(Atom [_]), rest] -> (h :) <$> charsOf rest
  Comp "." [h@(Int _), rest] -> (h :) <$> charsOf rest
  _ -> Nothing

elementsOf :: Term -> Maybe [Term]
elementsOf t = case t of
  Atom a | t /= Atom "[]" -> Just [ Atom [c] | c <- a ]
  Int i -> Just [ Atom [c] | c <- show i ]
  _ -> let go (Atom "[]") = Just []
           go (Comp "." [h, r]) = (h :) <$> go r
           go _ = Nothing
       in go t

substituteInputs :: [(Int, [Term])] -> Term -> Maybe Term
substituteInputs inputs val =
  let table = M.fromList [ (1000 * (i + 1) + q, c) | (i, cs) <- inputs, (q, c) <- zip [1 ..] cs ]
      sub (Var v _) = M.lookup v table
      sub (Comp f as) = Comp f <$> mapM sub as
      sub x = Just x
  in sub val

showChar' :: Term -> String
showChar' (Atom [c]) = [c]
showChar' (Int i) | i >= 0 && i < 1114112 = [toEnum (fromIntegral i)]
showChar' t = showTermQ t

-- ---------------------------------------------------------------------------
-- formula: closed forms per position

formulaCmd :: Flags -> FilePath -> String -> Int -> IO ()
formulaCmd fl file keyS n = do
  (p, evs) <- loadCutFree file
  key <- parseKey keyS
  (lo, hi) <- maybe (die' "formula needs --domain LO..HI") return (fDomain fl)
  let j = maybe (snd key - 1) (subtract 1) (fOutArg fl)
      d = fDomainArg fl - 1
      sr = slicePositions p key j n
      prog = runProgram (generated p sr key j n Nothing)
  mnnsDir <- case fMnns fl of
    Just dir -> return (Just dir)
    Nothing -> lookupEnv "MNNS_DIR"
  wrappers <- forM [1 .. n] $ \k -> do
    let sp = Spec key j k
        name = specName sp
        used = M.findWithDefault Set.empty sp (srUsed sr)
        arity = snd key
    if not (Set.isSubsetOf used (Set.singleton d))
      then do
        putStrLn ("char " ++ show k ++ ": uses other inputs too " ++ show (map (+ 1) (Set.toList used)) ++ "; kept as sliced code")
        return Nothing
      else do
        samples <- forM [lo .. hi] $ \x -> do
          let cVar = Var 0 "C"
              args = [ if i == j then cVar else if i == d then Int x else Atom "_" | i <- [0 .. arity - 1] ]
          return (either (const Nothing) id (firstValue prog (Comp name args) 1 cVar))
        case mapM codeOf samples of
          Nothing -> do
            putStrLn ("char " ++ show k ++ ": not defined on all of " ++ show lo ++ ".." ++ show hi ++ "; kept as sliced code")
            return Nothing
          Just codes -> do
            (formula, source) <- case mnnsDir of
              Just dir -> do
                r <- inferWithMnns dir codes
                case r of
                  Right f -> return (f, "mnns AlgebraPLOp")
                  Left why -> return (inferNative codes, "native mirror of mnns AlgebraPLOp (" ++ why ++ ")")
              Nothing -> return (inferNative codes, "native mirror of mnns AlgebraPLOp (no mnns given)")
            let native = inferNative codes
            case formula of
              Just f | and [ evalFormula f pos == c | (pos, c) <- zip [0 ..] codes ] -> do
                putStrLn ("char " ++ show k ++ ": code = " ++ showFormula f ++ " at P = N - " ++ show lo
                          ++ "   [" ++ source ++ (if Just f == native then "" else "; differs from native mirror") ++ "]")
                return (Just (sp, f, isCodeList samples))
              _ -> do
                putStrLn ("char " ++ show k ++ ": no formula (" ++ source ++ "); kept as sliced code")
                return Nothing
  let chosen = [ w | Just w <- wrappers ]
      renamed = M.fromList [ (sp, [ renameHead (specName sp ++ "__sliced") c | c <- M.findWithDefault [] sp (srClauses sr) ])
                           | (sp, _, _) <- chosen ]
      sr' = sr { srClauses = M.union renamed (srClauses sr) }
      formulaClauses = [ formulaClause sp f isCodes lo hi d | (sp, f, isCodes) <- chosen ]
  writeOut fl (header file evs sr ++ "% Positions with a formula are exact on the domain by exhaustion and use the\n"
                 ++ "% sliced program (NAME__charK__sliced) outside it.\n")
           (generated p sr' key j n (Just formulaClauses))
  where
    codeOf (Just (Atom [c])) = Just (fromIntegral (ord c))
    codeOf (Just (Int i)) = Just i
    codeOf _ = Nothing
    isCodeList ss = case ss of
      (Just (Int _) : _) -> True
      _ -> False
    renameHead nm (Clause h b nv) = Clause (Comp nm (goalArgs h)) b nv

-- | NAME__charK(..., N, ..., C) :- ( integer(N), Lo =< N =< Hi -> formula ; sliced ).
formulaClause :: Spec -> Formula -> Bool -> Integer -> Integer -> Int -> Clause
formulaClause sp@(Spec (_, arity) j _) f isCodes lo hi d =
  let nV = Var 0 "N"
      cV = Var 1 "C"
      pV = Var 2 "P"
      codeV = Var 3 "Code"
      others = [ Var (10 + i) "_" | i <- [0 .. arity - 1] ]
      args = [ if i == j then cV else if i == d then nV else others !! i | i <- [0 .. arity - 1] ]
      guard = mkConj [ Comp "integer" [nV], Comp ">=" [nV, Int lo], Comp "=<" [nV, Int hi] ]
      compute = mkConj ([ Comp "is" [pV, Comp "-" [nV, Int lo]], Comp "is" [codeV, formulaExpr f pV] ]
                        ++ [ if isCodes then Comp "=" [cV, codeV] else Comp "char_code" [cV, codeV] ])
      sliced = Comp (specName sp ++ "__sliced") args
  in Clause (Comp (specName sp) args) (Comp ";" [Comp "->" [guard, compute], sliced]) 20
