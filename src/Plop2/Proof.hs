-- | Independent checker for plop2 slice proofs.
--
-- Every clause of a per-character program comes with a slice_step:
-- the source clause, the result clause, which source goals were kept,
-- dropped (each with a totality certificate) or consumed, and the
-- derivation of the element expression.  This module re-checks each step
-- with its own analyses (first occurrences, groundness, certificates,
-- element rules) and does not use "Plop2.Slice".  It also regenerates the
-- wrapper and dispatcher clauses, checks formula clauses by exhaustive
-- evaluation, and checks input-character facts by symbolic evaluation.
module Plop2.Proof
  ( checkPlopProof
  , wrapperClauses
  , dispatcherClause
  , proofText
  , readProof
  ) where

import Control.Monad (forM, forM_, unless)
import qualified Data.IntSet as IS
import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Builtins (Ev(..))
import Detlog2.Interp
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Term

type Check a = Either String a

ensure :: Bool -> String -> Check ()
ensure b m = unless b (Left m)

proofText :: [Term] -> String
proofText steps = unlines ("% plop2 slice proof: one step per rewrite (see docs/proof_rules.md)."
                           : [ showTermQ s ++ "." | s <- steps ])

readProof :: String -> Either String [Term]
readProof src = do
  p <- parseProgram src
  return [ if clBody c == Atom "true" then clHead c else Comp ":-" [clHead c, clBody c]
         | (_, cs) <- programClauses p, c <- cs ]

-- ---------------------------------------------------------------------------
-- Names and templates (written independently of the generator)

data Sp = Sp PredKey Int Int deriving (Eq, Ord, Show)

spName :: Sp -> String
spName (Sp (f, n) j k)
  | j == n - 1 = f ++ "__char" ++ show k
  | otherwise = f ++ "__a" ++ show (j + 1) ++ "_char" ++ show k

dName :: PredKey -> Int -> Int -> String
dName (f, _) j k = f ++ "__a" ++ show (j + 1) ++ "_upto" ++ show k ++ "_r"

spOf :: Term -> Check Sp
spOf (Comp "spec" [Comp "/" [Atom f, Int n], Int j, Int k]) = return (Sp (f, fromIntegral n) (fromIntegral j) (fromIntegral k))
spOf t = Left ("bad spec " ++ showTermQ t)

-- | name__r(A.., R) :- once(name__alt(A.., R)).   name(A.., C) :- name__r(A.. c(C)).
wrapperClauses :: PredKey -> Int -> Int -> [Clause]
wrapperClauses key@(_, n) j k =
  let sp = Sp key j k
      as = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1] ]
      r = Var n "R"
      c = Var (n + 1) "C"
      argsR = [ if i == j then r else a | (i, a) <- zip [0 ..] as ]
      argsC = [ if i == j then c else a | (i, a) <- zip [0 ..] as ]
      argsCR = [ if i == j then Comp "c" [c] else a | (i, a) <- zip [0 ..] as ]
  in [ Clause (Comp (spName sp ++ "__r") argsR) (Comp "once" [Comp (spName sp ++ "__alt") argsR]) (n + 2)
     , Clause (Comp (spName sp) argsC) (Comp (spName sp ++ "__r") argsCR) (n + 2) ]

-- | disp(Others.., J, R) :- ( J =:= 1 -> q__char1__r(..R..) ; ... ; R = none ).
dispatcherClause :: PredKey -> Int -> Int -> Clause
dispatcherClause key@(_, n) j k =
  let others = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1], i /= j ]
      jv = Var n "J"
      r = Var (n + 1) "R"
      argsFor = let (b, a) = splitAt j others in b ++ [r] ++ a
      body = foldr (\kk e -> Comp ";" [Comp "->" [Comp "=:=" [jv, Int (fromIntegral kk)], Comp (spName (Sp key j kk) ++ "__r") argsFor], e])
                   (Comp "=" [r, Atom "none"]) [1 .. k]
  in Clause (Comp (dName key j k) (others ++ [jv, r])) body (n + 2)

-- ---------------------------------------------------------------------------
-- Entry point

-- | Check a generated program against its proof and the (cut-free)
-- source program.
checkPlopProof :: Program -> [Term] -> Program -> Check [String]
checkPlopProof src steps generated = do
  let slices = [ s | s@(Comp "slice_step" _) <- steps ]
  specs <- Set.fromList <$> mapM (\s -> case s of
                                          Comp "slice_step" (st : _) -> spOf st
                                          _ -> Left "bad step") slices
  -- used parameters of each program, recomputed from its result clauses
  resultClauses <- forM slices $ \s -> case s of
    Comp "slice_step" [st, _, _, resT, _, _] -> do
      sp <- spOf st
      c <- asClause resT
      return (sp, c)
    _ -> Left "bad slice_step"
  let usedOf sp@(Sp _ j _) = Set.unions [ usedParams j c | (sp', c) <- resultClauses, sp' == sp ]
      cx = Cx src specs usedOf
  justified <- forM slices (checkSlice cx)
  let dispNeeded = Set.fromList (concat [ ds | (_, ds) <- justified ])
      wrappers = concat [ wrapperClauses key j k | Sp key j k <- Set.toList specs ]
      disps = [ dispatcherClause key j k | (key, j, k) <- Set.toList dispNeeded ]
      helperKeys = Set.fromList (progOrder helperProgram)
  -- formula and input-character steps
  formulaCls <- forM [ s | s@(Comp "formula_step" _) <- steps ] (checkFormula generated)
  inputCls <- forM [ s | s@(Comp "input_chars_step" _) <- steps ] (checkInputChars generated)
  let formulaKeys = Set.fromList [ k' | c <- formulaCls, Just k' <- [goalKey (clHead c)] ]
      expected = [ c | (c, _) <- justified ] ++ [ w | w <- wrappers, maybe True (`Set.notMember` formulaKeys) (goalKey (clHead w)) ]
                 ++ disps ++ formulaCls ++ inputCls
      byKey = M.fromListWith (flip (++)) [ (k', [c]) | c <- expected, Just k' <- [goalKey (clHead c)] ]
      sourceKeys = Set.fromList (progOrder src)
  forM_ (programClauses generated) $ \(k', cs) ->
    if Set.member k' helperKeys || Set.member k' sourceKeys then do
      let reference = if Set.member k' helperKeys then progPreds helperProgram else progPreds src
      ensure (length cs == length (M.findWithDefault [] k' reference)
              && and (zipWith (\a b -> variant (emptyState 0) (clauseTerm a) (clauseTerm b)) cs (M.findWithDefault [] k' reference)))
             (showKey k' ++ ": differs from the " ++ (if Set.member k' helperKeys then "helper library" else "source"))
    else do
      js <- maybe (Left ("unjustified predicate " ++ showKey k')) return (M.lookup k' byKey)
      ensure (length js == length cs) (showKey k' ++ ": clause count differs from its proof")
      forM_ (zip cs js) $ \(a, b) ->
        ensure (variant (emptyState 0) (clauseTerm a) (clauseTerm b))
               (showKey k' ++ ": a clause differs from its proof:\n  program: " ++ showTermQ (clauseTerm a)
                ++ "\n  proof:   " ++ showTermQ (clauseTerm b))
  forM_ (M.keys byKey) $ \k' -> ensure (M.member k' (progPreds generated)) ("justified but missing: " ++ showKey k')
  return ["proof accepted: " ++ show (length slices) ++ " slice steps, "
          ++ show (length formulaCls) ++ " formula steps, " ++ show (length inputCls) ++ " input-character steps"]

helperProgram :: Program
helperProgram = either (const emptyProgram) id (parseProgram helperText)
  where helperText = helperSourceCopy

-- the helpers are part of the language plop2 targets; they are compared
-- with this copy (see docs/proof_rules.md for their lemmas)
helperSourceCopy :: String
helperSourceCopy = unlines
  [ "plop2_nth_r(K, T, R) :- ( plop2_nth_char(K, T, C) -> R = c(C) ; R = none )."
  , "plop2_nth_char(K, T, C) :- ( integer(T) -> plop2_int_char(K, T, C) ; atom(T) -> B is K - 1, sub_atom(T, B, 1, _, C) ; nth1(K, T, C) )."
  , "plop2_int_char(K, N, C) :- ( N < 0 -> ( K =:= 1 -> C = '-' ; K1 is K - 1, M is -N, plop2_int_char(K1, M, C) ) ; plop2_ndigits(N, D), K >= 1, K =< D, Digit is (N // 10 ^ (D - K)) mod 10, Code is 0'0 + Digit, char_code(C, Code) )."
  , "plop2_ndigits(N, D) :- ( N < 10 -> D = 1 ; M is N // 10, plop2_ndigits(M, D0), D is D0 + 1 )."
  , "plop2_chain(_, [], none)."
  , "plop2_chain(K, [P|Ps], R) :- call(P, K, R0), ( R0 = c(_) -> R = R0 ; plop2_part_length(P, K, L), K1 is K - L, plop2_chain(K1, Ps, R) )."
  , "plop2_part_length(P, K, L) :- K1 is K - 1, ( K1 =:= 0 -> L = 0 ; call(P, K1, R1), ( R1 = c(_) -> L = K1 ; plop2_part_length(P, K1, L) ) )."
  , "plop2_static(Es, J, R) :- plop2_nth_r(J, Es, R)."
  , "plop2_value(V, J, R) :- plop2_nth_r(J, V, R)."
  , "plop2_chain_c(Parts, J, R) :- plop2_chain(J, Parts, R)."
  ]

showKey :: PredKey -> String
showKey (f, n) = f ++ "/" ++ show n

asClause :: Term -> Check Clause
asClause t = case t of
  Comp ":-" [h, b] -> return (Clause h b (maxVarId t + 1))
  h | isCallable h -> return (Clause h (Atom "true") (maxVarId t + 1))
  _ -> Left ("not a clause: " ++ showTermQ t)

listOf :: Term -> Check [Term]
listOf (Atom "[]") = return []
listOf (Comp "." [h, t]) = (h :) <$> listOf t
listOf t = Left ("not a list: " ++ showTermQ t)

intsOf :: Term -> Check [Int]
intsOf t = listOf t >>= mapM (\x -> case x of
                                      Int i -> return (fromIntegral i)
                                      _ -> Left "not an index")

usedParams :: Int -> Clause -> Set.Set Int
usedParams j (Clause h b _) =
  let args = goalArgs h
      occ t = case t of
        Var v _ -> [v]
        Comp _ as -> concatMap occ as
        _ -> []
      counts = M.fromListWith (+) [ (v, 1 :: Int) | v <- concatMap occ (args ++ [b]) ]
  in Set.fromList [ ix | (ix, a) <- zip [0 ..] args, ix /= j
                       , not (isVar a) || any (\v -> M.findWithDefault 0 v counts > 1) (IS.toList (termVarIds a)) ]

-- ---------------------------------------------------------------------------
-- Slices

data Cx = Cx
  { cxSrc :: Program
  , cxSpecs :: Set.Set Sp
  , cxUsed :: Sp -> Set.Set Int
  }

-- | A scope: its goals, and the variables bound and ground before them.
data Scope = Scope { scGoals :: [Term], scBound :: IS.IntSet, scGround :: IS.IntSet }

checkSlice :: Cx -> Term -> Check (Clause, [(PredKey, Int, Int)])
checkSlice cx s = case s of
  Comp "slice_step" [st, Int i, srcT, resT, slT, node] -> do
    sp@(Sp key j k) <- spOf st
    src <- asClause srcT
    res <- asClause resT
    let here = spName sp ++ " clause " ++ show i ++ ": "
        baseCls = M.findWithDefault [] key (progPreds (cxSrc cx))
    ensure (i >= 1 && fromIntegral i <= length baseCls) (here ++ "no such source clause")
    let base = baseCls !! (fromIntegral i - 1)
    ensure (variant (emptyState 0) (clauseTerm base) (clauseTerm src)) (here ++ "not the source clause")
    let args = goalArgs (clHead src)
        inputs = [ a | (ix, a) <- zip [0 ..] args, ix /= j ]
        bound0 = IS.unions (map termVarIds inputs)
        srcVars = termVarIds (clauseTerm src)
        gs = conjList (clBody src)
        top = Scope gs bound0 bound0
    (r, e) <- case (clHead res, clBody res) of
      (Comp nm rargs, b) | nm == spName sp ++ "__alt" && length rargs == length args -> do
        let r = rargs !! j
        ensure (and [ a == b' | (ix, a, b') <- zip3 [0 :: Int ..] args rargs, ix /= j ]) (here ++ "inputs differ")
        ensure (isFreshIn srcVars r) (here ++ "the result variable is not fresh")
        return (r, b)
      _ -> Left (here ++ "wrong head")
    (kept, dropped, consumedIx) <- sliceOf slT
    checkPartition here (length gs) kept dropped consumedIx
    checkCerts here (cxSrc cx) top dropped
    -- the body is the kept goals and then the element expression
    let keptGoals = [ g | (ix, g) <- zip [1 ..] gs, ix `elem` kept ]
    ensure (nodeGoal node /= Nothing) (here ++ "bad derivation")
    let Just eGoal = nodeGoal node
    ensure (e == mkConj (keptGoals ++ [eGoal])) (here ++ "body is not the kept goals followed by the element expression")
    -- the element derivation, in the clause's scope
    res' <- checkNode cx here srcVars top (args !! j) (fromIntegral k) r node
    let consumedGoals = [ g | (ix, g) <- zip [1 ..] gs, ix `elem` consumedIx ]
    ensure (Set.fromList (map showTermQ (nrConsumed res')) == Set.fromList (map showTermQ consumedGoals))
           (here ++ "consumed goals differ from the derivation's producers")
    -- what the expression reads must be bound by the inputs or by kept goals
    let prodKept = IS.unions [ p | (ix, (_, p)) <- zip [1 ..] (produced bound0 gs), ix `elem` kept ]
        readable = bound0 `IS.union` prodKept
    ensure (IS.isSubsetOf (nrNeeds res') readable) (here ++ "the element expression reads a variable no kept goal binds")
    -- consumed goals' variables are not read by kept goals
    let prodConsumed = IS.unions [ p | (ix, (_, p)) <- zip [1 ..] (produced bound0 gs), ix `elem` consumedIx ]
    ensure (IS.null (IS.intersection prodConsumed (IS.unions (map termVarIds keptGoals))))
           (here ++ "a kept goal reads a variable of a consumed goal")
    ensure (distinctIds (nrFresh res')) (here ++ "a fresh variable is introduced twice")
    return (res, nrDisp res')
  _ -> Left "bad slice_step"

sliceOf :: Term -> Check ([Int], [(Int, Term)], [Int])
sliceOf (Comp "sl" [k, d, c]) = do
  kept <- intsOf k
  ds <- listOf d >>= mapM (\x -> case x of
                                   Comp "drop" [Int i, cert] -> return (fromIntegral i, cert)
                                   _ -> Left "bad drop")
  cons <- intsOf c
  return (kept, ds, cons)
sliceOf t = Left ("bad slice " ++ showTermQ t)

checkPartition :: String -> Int -> [Int] -> [(Int, Term)] -> [Int] -> Check ()
checkPartition here n kept dropped consumed = do
  let all' = kept ++ map fst dropped ++ consumed
  ensure (length all' == n && Set.fromList all' == Set.fromList [1 .. n])
         (here ++ "every goal must be kept, dropped with a certificate, or consumed")

produced :: IS.IntSet -> [Term] -> [(Term, IS.IntSet)]
produced bound = go bound
  where
    go _ [] = []
    go seen (g : gs) = let vs = termVarIds g in (g, vs `IS.difference` seen) : go (seen `IS.union` vs) gs

-- | Groundness (the checker's own copy of the rules).
gAfter :: IS.IntSet -> Term -> IS.IntSet
gAfter gr g = case g of
  Comp "=" [a, b]
    | gnd a -> gr `IS.union` termVarIds b
    | gnd b -> gr `IS.union` termVarIds a
  Comp "is" [x, e] | gnd e -> gr `IS.union` termVarIds x
  Comp f as@(_ : _)
    | (f, length as) `elem` fun && all gnd (init as) -> gr `IS.union` termVarIds (last as)
    | (f, length as) `elem` rev && gnd (last as) -> gr `IS.union` IS.unions (map termVarIds (init as))
  _ -> gr
  where
    gnd t = IS.isSubsetOf (termVarIds t) gr
    fun = [ ("atom_codes", 2), ("atom_chars", 2), ("number_codes", 2), ("number_chars", 2)
          , ("atom_length", 2), ("char_code", 2), ("upcase_atom", 2), ("downcase_atom", 2)
          , ("atomic_list_concat", 2), ("atomic_list_concat", 3), ("atom_concat", 3)
          , ("string_concat", 3), ("string_chars", 2), ("atom_string", 2)
          , ("append", 3), ("reverse", 2), ("length", 2), ("nth0", 3), ("nth1", 3)
          , ("last", 2), ("sum_list", 2), ("max_list", 2), ("min_list", 2), ("msort", 2), ("sort", 2)
          , ("succ", 2), ("plus", 3) ]
    rev = [ ("atom_codes", 2), ("atom_chars", 2), ("char_code", 2), ("string_chars", 2) ]

groundBefore :: Scope -> Int -> IS.IntSet
groundBefore sc ix = foldl' gAfter (scGround sc) (take (ix - 1) (scGoals sc))

-- | Re-check every totality certificate.
checkCerts :: String -> Program -> Scope -> [(Int, Term)] -> Check ()
checkCerts here prog sc dropped =
  forM_ dropped $ \(ix, cert) -> do
    let g = scGoals sc !! (ix - 1)
        prod = snd (produced (scBound sc) (scGoals sc) !! (ix - 1))
        gnd = groundBefore sc ix
        gr t = IS.isSubsetOf (termVarIds t) gnd
        freshV x t = IS.member x prod && not (IS.member x (termVarIds t))
        isArith t = case t of
          Int _ -> True
          Var _ _ -> True
          Comp op [a, b] | op `elem` ["+", "-", "*"] -> isArith a && isArith b
          Comp "-" [a] -> isArith a
          _ -> False
        userDefined = maybe False (`M.member` progPreds prog) (goalKey g)
        ok = case (cert, goalKey g) of
          (Comp "total" [Comp "pred" [Comp "/" [Atom f, Int n], modeT]], Just key)
            | key == (f, fromIntegral n), userDefined, Right ins <- intsOf modeT ->
                callModeOk ins g prod gnd && totalPred prog Set.empty Nothing key ins
          _ -> not userDefined && builtinOk
        builtinOk = case (cert, g) of
          (Comp "total" [Atom "true"], Atom "true") -> True
          (Comp "total" [Atom "output"], Atom "nl") -> True
          (Comp "total" [Atom "output"], Comp f [_]) -> f `elem` ["write", "print", "writeln", "writeq", "write_canonical"]
          (Comp "total" [Atom "fresh_unify"], Comp "=" [a, b]) ->
            (case a of { Var x _ -> freshV x b; _ -> False }) || (case b of { Var x _ -> freshV x a; _ -> False })
          (Comp "total" [Atom "arith"], Comp "is" [Var x _, e']) -> freshV x e' && gr e' && isArith e'
          (Comp "total" [Atom "text"], Comp "char_code" [Var x _, code]) -> gr code && freshV x code
          (Comp "total" [Atom "text"], Comp f [a, Var x _]) ->
            f `elem` ["atom_codes", "atom_chars", "atom_length", "number_codes", "number_chars", "upcase_atom", "downcase_atom", "atomic_list_concat"]
            && gr a && freshV x a
          (Comp "total" [Atom "text"], Comp "atomic_list_concat" [l, sp, Var x _]) -> gr l && gr sp && freshV x (Comp "x" [l, sp])
          (Comp "total" [Atom "text"], Comp f [a, b, Var x _]) -> f `elem` ["atom_concat", "string_concat"] && gr a && gr b && freshV x (Comp "x" [a, b])
          (Comp "total" [Atom "append"], Comp "append" [a, b, Var x _]) -> gr a && freshV x (Comp "x" [a, b])
          (Comp "total" [Atom "length"], Comp "length" [l, Var x _]) -> gr l && freshV x l
          (Comp "total" [Atom "reverse"], Comp "reverse" [l, Var x _]) -> gr l && freshV x l
          _ -> False
    ensure ok (here ++ "goal " ++ show ix ++ " (" ++ showTermQ g ++ ") is dropped without a valid totality certificate")

-- | A call in a mode: the input positions are ground, the others are
-- distinct variables that first occur here and not in the inputs.
callModeOk :: [Int] -> Term -> IS.IntSet -> IS.IntSet -> Bool
callModeOk ins g prod gnd =
  let as = goalArgs g
      inVars = IS.unions [ termVarIds a | (i, a) <- zip [0 ..] as, i `elem` ins ]
      outs = [ a | (i, a) <- zip [0 ..] as, i `notElem` ins ]
  in all (\i -> i < length as && IS.isSubsetOf (termVarIds (as !! i)) gnd) ins
     && all (\a -> case a of
                     Var x _ -> IS.member x prod && not (IS.member x inVars)
                     _ -> False) outs
     && length (Set.fromList [ x | Var x _ <- outs ]) == length outs

-- | Totality of a predicate in a mode (the checker's own derivation; see
-- docs/proof_rules.md, rule TOTAL).
totalPred :: Program -> Set.Set PredKey -> Maybe (PredKey, [Int], Int, Int) -> PredKey -> [Int] -> Bool
totalPred prog visiting _ key ins
  | Set.member key visiting = False
  | otherwise = case M.findWithDefault [] key (progPreds prog) of
      [c] -> plainInputs c (-1) && body c Nothing
      [a, b] -> or [ sw a b i || sw b a i | i <- ins ]
      _ -> False
  where
    hargs c = goalArgs (clHead c)
    plainInputs c skip =
      let xs = [ x | (i, x) <- zip [0 ..] (hargs c), i `elem` ins, i /= skip ]
      in all isVar xs && length (Set.fromList [ v | Var v _ <- xs ]) == length xs
    sw cn cc i = case (hargs cn !! i, hargs cc !! i) of
      (Atom "[]", Comp "." [Var hv _, Var tv _]) ->
        hv /= tv && plainInputs cn i && plainInputs cc i
        && and [ not (IS.member hv (termVarIds x)) && not (IS.member tv (termVarIds x))
               | (j, x) <- zip [0 ..] (hargs cc), j `elem` ins, j /= i ]
        && body cn Nothing && body cc (Just (i, tv))
      _ -> False
    body c rec' =
      let gnd0 = IS.unions [ termVarIds x | (i, x) <- zip [0 ..] (hargs c), i `elem` ins ]
          seen0 = gnd0   -- output-only head variables are fresh in this mode
          go _ _ [] = True
          go gnd seen (g : gs) =
            let prod = termVarIds g `IS.difference` seen
            in goalTotal gnd prod g && go (gAfter gnd g) (seen `IS.union` termVarIds g) gs
          goalTotal gnd prod g = case goalKey g of
            Just k | k == key, Just (i, tv) <- rec' ->
              callModeOk ins g prod gnd && case goalArgs g !! i of
                Var x _ -> x == tv
                _ -> False
            Just k | M.member k (progPreds prog) ->
              let as = goalArgs g
                  ins' = [ j | (j, a) <- zip [0 ..] as, IS.isSubsetOf (termVarIds a) gnd ]
              in callModeOk ins' g prod gnd && totalPred prog (Set.insert key visiting) Nothing k ins'
            _ -> builtinTotal gnd prod g
      in go gnd0 seen0 (conjList (clBody c))

-- | The built-in totality rules (the same list as for dropped goals).
builtinTotal :: IS.IntSet -> IS.IntSet -> Term -> Bool
builtinTotal gnd prod g = case g of
  Atom "true" -> True
  Atom "nl" -> True
  Comp f [_] | f `elem` ["write", "print", "writeln", "writeq", "write_canonical"] -> True
  Comp "=" [Var x _, t] | freshV x t -> True
  Comp "=" [t, Var x _] | freshV x t -> True
  Comp "is" [Var x _, e] -> freshV x e && gr e && isArith e
  Comp "char_code" [Var x _, code] -> gr code && freshV x code
  Comp f [a, Var x _] | f `elem` ["atom_codes", "atom_chars", "atom_length", "number_codes", "number_chars", "upcase_atom", "downcase_atom", "atomic_list_concat"] ->
    gr a && freshV x a
  Comp "atomic_list_concat" [l, sp, Var x _] -> gr l && gr sp && freshV x (Comp "x" [l, sp])
  Comp f [a, b, Var x _] | f `elem` ["atom_concat", "string_concat"] -> gr a && gr b && freshV x (Comp "x" [a, b])
  Comp "append" [a, b, Var x _] -> gr a && freshV x (Comp "x" [a, b])
  Comp "length" [l, Var x _] -> gr l && freshV x l
  Comp "reverse" [l, Var x _] -> gr l && freshV x l
  _ -> False
  where
    gr t = IS.isSubsetOf (termVarIds t) gnd
    freshV x t = IS.member x prod && not (IS.member x (termVarIds t))
    isArith t = case t of
      Int _ -> True
      Var _ _ -> True
      Comp op [a, b] | op `elem` ["+", "-", "*"] -> isArith a && isArith b
      Comp "-" [a] -> isArith a
      _ -> False

-- ---------------------------------------------------------------------------
-- Element derivations

data NR = NR { nrConsumed :: [Term], nrNeeds :: IS.IntSet, nrFresh :: [Int], nrDisp :: [(PredKey, Int, Int)] }

instance Semigroup NR where
  NR a b c d <> NR a' b' c' d' = NR (a ++ a') (IS.union b b') (c ++ c') (d ++ d')
instance Monoid NR where
  mempty = NR [] IS.empty [] []

nodeGoal :: Term -> Maybe Term
nodeGoal (Comp "e" [_, _, _, _, g, _, _]) = Just g
nodeGoal _ = Nothing

isFreshIn :: IS.IntSet -> Term -> Bool
isFreshIn srcVars t = case t of
  Var i _ -> not (IS.member i srcVars)
  _ -> False

distinctIds :: [Int] -> Bool
distinctIds is = IS.size (IS.fromList is) == length is

-- | First-occurrence producer of V among the scope's goals.
producerIn :: Scope -> Int -> Maybe (Int, Term)
producerIn sc v =
  case [ (ix, g) | (ix, (g, p)) <- zip [1 ..] (produced (scBound sc) (scGoals sc)), IS.member v p ] of
    (x : _) -> Just x
    [] -> Nothing

-- | Check a derivation node for element K of Subject into R, in a scope.
checkNode :: Cx -> String -> IS.IntSet -> Scope -> Term -> Int -> Term -> Term -> Check NR
checkNode cx here srcVars sc subject k r node = case node of
  Comp "e" [Atom rule, subj, Int kk, r', goal, subsT, info] -> do
    subs <- listOf subsT
    let h = here ++ rule ++ " for element " ++ show k ++ " of " ++ take 80 (showTermQ subject) ++ ": "
        need b m = ensure b (h ++ m)
        needsOf t = IS.intersection (termVarIds t) srcVars
        freshVars ts = do
          need (all (isFreshIn srcVars) ts) "a new variable is not fresh"
          return [ i | Var i _ <- ts ]
        none' = Comp "=" [r, Atom "none"]
        cOf x = Comp "c" [x]
        ite c t e = Comp ";" [Comp "->" [c, t], e]
        sub0 = case subs of
          (x : _) -> return x
          [] -> Left (h ++ "missing sub-derivation")
        -- the producer of the subject variable in this scope
        recorded = case info of
          Comp "branch" (g : _) -> g
          _ -> info
        producerOfSubject = case subject of
          Var v _ -> case producerIn sc v of
            Just (ix, g) | g == recorded -> return (ix, g)
            _ -> Left (h ++ "the recorded goal is not the first producer of the subject")
          _ -> Left (h ++ "subject is not a variable")
        before ix = sc { scGoals = take (ix - 1) (scGoals sc) }
        isSubj x = x == subject
    need (subj == subject && fromIntegral kk == k && r' == r) "node is for another element"
    case rule of
      "el_head" -> case subject of
        Comp "." [hd, _] | k == 1 -> need (goal == Comp "=" [r, cOf hd]) "template" >> return mempty { nrNeeds = needsOf hd }
        _ -> Left (h ++ "not a list cell")
      "el_tail" -> case subject of
        Comp "." [_, tl] | k > 1 -> do
          s0 <- sub0
          need (Just goal == nodeGoal s0) "template"
          checkNode cx here srcVars sc tl (k - 1) r s0
        _ -> Left (h ++ "not a list cell")
      "el_none" -> do
        need (goal == none') "template"
        let shortText s = length s < k
        need (case subject of
                Atom "[]" -> True
                Atom a -> shortText a
                Int x -> shortText (show x)
                Var v _ -> producerIn sc v == Nothing && not (IS.member v (scBound sc))
                _ -> False) "the subject may have an element here"
        return mempty
      "el_const" -> do
        let text = case subject of
              Atom a -> Just a
              Int x -> Just (show x)
              _ -> Nothing
        case text of
          Just s | k <= length s -> need (goal == Comp "=" [r, cOf (Atom [s !! (k - 1)])]) "template" >> return mempty
          _ -> Left (h ++ "not a constant with this element")
      "el_nth" -> do
        need (goal == Comp "plop2_nth_r" [Int (fromIntegral k), subject, r]) "template"
        return mempty { nrNeeds = needsOf subject }
      "el_unify" -> do
        (ix, g) <- producerOfSubject
        t <- case g of
          Comp "=" [x, t] | isSubj x -> return t
          Comp "=" [t, x] | isSubj x -> return t
          _ -> Left (h ++ "producer is not a unification")
        s0 <- sub0
        need (Just goal == nodeGoal s0) "template"
        nr <- checkNode cx here srcVars (before ix) t k r s0
        return nr { nrConsumed = g : nrConsumed nr }
      "el_alias" -> do
        (ix, g) <- producerOfSubject
        w <- case g of
          Comp "=" [x, y@(Var _ _)] | isSubj x -> return y
          Comp "=" [y@(Var _ _), x] | isSubj x -> return y
          _ -> Left (h ++ "producer is not an alias")
        let seenBefore = scBound sc `IS.union` IS.unions (map termVarIds (take (ix - 1) (scGoals sc)))
            wId = case w of
              Var i _ -> i
              _ -> -1
        need (not (IS.member wId seenBefore)) "the alias's other variable occurs earlier"
        s0 <- sub0
        need (Just goal == nodeGoal s0) "template"
        let sc' = sc { scGoals = take (ix - 1) (scGoals sc) ++ drop ix (scGoals sc) }
        nr <- checkNode cx here srcVars sc' w k r s0
        return nr { nrConsumed = g : nrConsumed nr }
      "el_same_text" -> do
        (ix, g) <- producerOfSubject
        t <- case g of
          Comp f [a, x] | isSubj x, f `elem` ["atom_chars", "string_chars", "atom_string"] -> return a
          Comp f [x, l] | isSubj x, f `elem` ["atom_chars", "string_chars"] -> return l
          _ -> Left (h ++ "producer")
        s0 <- sub0
        need (Just goal == nodeGoal s0) "template"
        nr <- checkNode cx here srcVars (before ix) t k r s0
        return nr { nrConsumed = g : nrConsumed nr }
      _ | rule `elem` ["el_codes_of_text", "el_text_of_codes"] -> do
        (ix, g) <- producerOfSubject
        t <- case (rule, g) of
          ("el_codes_of_text", Comp "atom_codes" [a, x]) | isSubj x -> return a
          ("el_text_of_codes", Comp "atom_codes" [x, l]) | isSubj x -> return l
          _ -> Left (h ++ "producer")
        s0 <- sub0
        (r0, ch, code) <- case nodeGoal s0 >>= \sg -> Just (sg, goal) of
          Just (sg, Comp "," [sg', Comp ";" [Comp "->" [Comp "=" [r0, Comp "c" [tv]], Comp "," [Comp "char_code" [ch, code], Comp "=" [r2, Comp "c" [res]]]], Comp "=" [r3, Atom "none"]]])
            | sg == sg' && r2 == r && r3 == r
            , (rule == "el_codes_of_text" && tv == ch && res == code) || (rule == "el_text_of_codes" && tv == code && res == ch) ->
                return (r0, ch, code)
          _ -> Left (h ++ "template")
        fr <- freshVars [r0, ch, code]
        nr <- checkNode cx here srcVars (before ix) t k r0 s0
        return nr { nrConsumed = g : nrConsumed nr, nrFresh = fr ++ nrFresh nr }
      "el_number_codes" -> do
        (_, g) <- producerOfSubject
        num <- case g of
          Comp "number_codes" [n', x] | isSubj x -> return n'
          _ -> Left (h ++ "producer")
        case goal of
          Comp "," [Comp "plop2_nth_r" [Int k', n', r0], Comp ";" [Comp "->" [Comp "=" [r0', Comp "c" [ch]], Comp "," [Comp "char_code" [ch', code], Comp "=" [r2, Comp "c" [code']]]], Comp "=" [r3, Atom "none"]]]
            | fromIntegral k' == k && n' == num && r0' == r0 && ch' == ch && code' == code && r2 == r && r3 == r -> do
                fr <- freshVars [r0, ch, code]
                return (NR [g] (needsOf num) fr [])
          _ -> Left (h ++ "template")
      "el_number_chars" -> do
        (_, g) <- producerOfSubject
        num <- case g of
          Comp "number_chars" [n', x] | isSubj x -> return n'
          Comp "atom_number" [x, n'] | isSubj x -> return n'
          _ -> Left (h ++ "producer")
        need (goal == Comp "plop2_nth_r" [Int (fromIntegral k), num, r]) "template"
        return (NR [g] (needsOf num) [] [])
      "el_reverse" -> do
        (_, g) <- producerOfSubject
        l <- case g of
          Comp "reverse" [l, x] | isSubj x -> return l
          _ -> Left (h ++ "producer")
        case conjList goal of
          [ Comp "length" [l', len], Comp "is" [ix, Comp "+" [Comp "-" [len', Int k'], Int 1]]
            , Comp ";" [Comp "->" [Comp ">=" [ix', Int 1], Comp "," [Comp "nth1" [ix'', l'', xv], Comp "=" [r2, Comp "c" [xv']]]], Comp "=" [r3, Atom "none"]] ]
            | l' == l && l'' == l && len' == len && ix' == ix && ix'' == ix && xv' == xv && fromIntegral k' == k && r2 == r && r3 == r -> do
                fr <- freshVars [len, ix, xv]
                return (NR [g] (needsOf l) fr [])
          _ -> Left (h ++ "template")
      "el_maplist" -> do
        (ix, g) <- producerOfSubject
        (f, l) <- case g of
          Comp "maplist" [f, l, x] | isSubj x, not (isVar f) -> return (f, l)
          _ -> Left (h ++ "producer")
        s0 <- sub0
        case goal of
          Comp "," [sg, Comp ";" [Comp "->" [Comp "=" [r0, Comp "c" [xv]], Comp "," [call, Comp "=" [r2, Comp "c" [yv]]]], Comp "=" [r3, Atom "none"]]]
            | Just sg == nodeGoal s0 && Just call == addArgs f [xv, yv] && r2 == r && r3 == r -> do
                fr <- freshVars [r0, xv, yv]
                nr <- checkNode cx here srcVars (before ix) l k r0 s0
                return nr { nrConsumed = g : nrConsumed nr, nrFresh = fr ++ nrFresh nr, nrNeeds = nrNeeds nr `IS.union` needsOf f }
          _ -> Left (h ++ "template")
      "el_spec" -> do
        (ix, g) <- producerOfSubject
        key <- maybe (Left (h ++ "producer is not callable")) return (goalKey g)
        need (M.member key (progPreds (cxSrc cx))) "producer is not a user predicate"
        let gargs = goalArgs g
        pos <- case [ i | (i, a) <- zip [0 ..] gargs, isSubj a ] of
          [p] -> return p
          _ -> Left (h ++ "the subject is not exactly one argument of the producer")
        need (not (any (\(i, a) -> i /= pos && IS.member (subjId subject) (termVarIds a)) (zip [0 ..] gargs))) "the subject also occurs in another argument"
        let sp = Sp key pos k
            used = cxUsed cx sp
            gnd = groundBefore sc ix
        need (Set.member sp (cxSpecs cx)) "the callee's program for this position is missing"
        case goal of
          Comp nm args' | nm == spName sp ++ "__r" && length args' == length gargs -> do
            frs <- forM (zip3 [0 ..] gargs args') $ \(i, a, b) ->
              if i == pos then need (b == r) "result position" >> return []
              else if Set.member i used then do
                need (a == b) "an argument the callee reads is not passed"
                need (IS.isSubsetOf (termVarIds a) gnd) "an argument the callee reads is not ground at the call"
                return []
              else freshVars [b]
            return (NR [g] (IS.unions [ needsOf b | (i, b) <- zip [0 ..] args', i /= pos ]) (concat frs) [])
          _ -> Left (h ++ "template")
      "el_chain" -> do
        (ix, g) <- producerOfSubject
        (mode, parts) <- case g of
          Comp "append" [a, b, x] | isSubj x -> return (False, [a, b])
          Comp f [a, b, x] | isSubj x, f `elem` ["atom_concat", "string_concat"] -> return (True, [a, b])
          Comp "atomic_list_concat" [l, x] | isSubj x -> (,) True <$> listOf l
          Comp "atomic_list_concat" [l, sp, x] | isSubj x -> (\ps -> (True, interleaveC sp ps)) <$> listOf l
          _ -> Left (h ++ "producer is not a concatenation")
        need (length subs == length parts) "one closure per part"
        clos <- forM (zip parts subs) $ \(p, cl) -> checkClosure cx h srcVars (before ix) mode k p cl
        need (goal == Comp "plop2_chain" [Int (fromIntegral k), mkList [ c | (c, _) <- clos ] (Atom "[]"), r]) "template"
        return (mconcat (map snd clos)) { nrConsumed = g : concatMap (nrConsumed . snd) clos }
      "el_chain_const" -> do
        (ix, g) <- producerOfSubject
        (mode, parts) <- case g of
          Comp "append" [a, b, x] | isSubj x -> return (False, [a, b])
          Comp f [a, b, x] | isSubj x, f `elem` ["atom_concat", "string_concat"] -> return (True, [a, b])
          Comp "atomic_list_concat" [l, x] | isSubj x -> (,) True <$> listOf l
          Comp "atomic_list_concat" [l, sp, x] | isSubj x -> (\ps -> (True, interleaveC sp ps)) <$> listOf l
          _ -> Left (h ++ "producer is not a concatenation")
        need (length subs == length parts) "one closure per part"
        clos <- forM (zip parts subs) $ \(p, cl) -> checkClosure cx h srcVars (before ix) mode k p cl
        let (prefix, _) = closurePrefixC [ c | (c, _) <- clos ]
        need (k <= length prefix && goal == Comp "=" [r, cOf (prefix !! (k - 1))]) "element is not in the static prefix"
        -- only the concatenations are consumed; any producer of a later part is left to the slice
        let chainGoals = [ pg | Comp "cl" [Atom "cl_chain", _, _, Comp "chain" [pg, _]] <- subs ]
        return mempty { nrConsumed = g : chainGoals }
      "el_branch" -> do
        (ix, g) <- producerOfSubject
        (mc, t, e) <- case g of
          Comp ";" [Comp "->" [c, t], e] -> return (Just c, t, e)
          Comp "->" [c, t] -> return (Just c, t, Atom "fail")
          Comp "if_commit" [c, t, e] -> return (Just c, t, e)
          Comp ";" [a, b] -> return (Nothing, a, b)
          _ -> Left (h ++ "producer is not a branch")
        (slC, slT, slE) <- case info of
          Comp "branch" [_, a, b, c] -> (,,) <$> sliceOf a <*> sliceOf b <*> sliceOf c
          _ -> Left (h ++ "branch slices")
        (nT, nE) <- case subs of
          [a, b] -> return (a, b)
          _ -> Left (h ++ "two branch derivations")
        let cs = maybe [] conjList mc
            ts = conjList t
            es = conjList e
            beforeGs = take (ix - 1) (scGoals sc)
            boundB = scBound sc `IS.union` IS.unions (map termVarIds beforeGs)
            groundB = groundBefore sc ix
            scC = Scope cs boundB groundB
            scT = Scope ts (boundB `IS.union` IS.unions (map termVarIds cs)) (foldl' gAfter groundB cs)
            scE = Scope es boundB groundB
            pick (kept, _, _) xs = [ x | (i, x) <- zip [1 ..] xs, i `elem` kept ]
        forM_ [(slC, cs, scC), (slT, ts, scT), (slE, es, scE)] $ \((kp, dr, co), xs, scx) -> do
          checkPartition h (length xs) kp dr co
          checkCerts h (cxSrc cx) scx dr
        gT <- maybe (Left (h ++ "then derivation")) return (nodeGoal nT)
        gE <- maybe (Left (h ++ "else derivation")) return (nodeGoal nE)
        let thenG = mkConj (pick slT ts ++ [gT])
            elseG = mkConj (pick slE es ++ [gE])
            expected = case (mc, g) of
              (Nothing, _) -> Comp ";" [thenG, elseG]
              (Just _, Comp "if_commit" _) -> Comp "if_commit" [mkConj (pick slC cs), thenG, elseG]
              (Just _, _) -> ite (mkConj (pick slC cs)) thenG elseG
        need (goal == expected) "template"
        nrT <- checkNode cx here srcVars (Scope (beforeGs ++ cs ++ ts) (scBound sc) (scGround sc)) subject k r nT
        nrE <- checkNode cx here srcVars (Scope (beforeGs ++ es) (scBound sc) (scGround sc)) subject k r nE
        -- consumed goals of each branch scope must be its consumed indices
        let consumedIn (_, _, co) xs = [ x | (i, x) <- zip [1 ..] xs, i `elem` co ]
            local = cs ++ ts ++ es
            claimed = consumedIn slC cs ++ consumedIn slT ts ++ consumedIn slE es
            fromNodes = filter (`elem` local) (nrConsumed nrT ++ nrConsumed nrE)
        need (Set.fromList (map showTermQ claimed) == Set.fromList (map showTermQ fromNodes)) "branch consumption"
        -- reads inside a branch come from kept goals of the branch or from outside
        let keptProd sl scx = IS.unions [ p | (i, (_, p)) <- zip [1 ..] (produced (scBound scx) (scGoals scx)), let (kp, _, _) = sl, i `elem` kp ]
            readT = IS.unions [IS.intersection (IS.unions (map termVarIds (pick slT ts))) srcVars, nrNeeds nrT]
            readE = IS.unions [IS.intersection (IS.unions (map termVarIds (pick slE es))) srcVars, nrNeeds nrE]
            readC = IS.intersection (IS.unions (map termVarIds (pick slC cs))) srcVars
            prodC = IS.unions (map termVarIds cs) `IS.difference` boundB
            prodT = IS.unions (map termVarIds ts) `IS.difference` scBound scT
            prodE = IS.unions (map termVarIds es) `IS.difference` boundB
        need (IS.null (IS.intersection readT (prodT `IS.difference` keptProd slT scT))) "then-branch reads a dropped goal's variable"
        need (IS.null (IS.intersection readT (prodC `IS.difference` keptProd slC scC))) "then-branch reads a dropped condition variable"
        need (IS.null (IS.intersection readE (prodE `IS.difference` keptProd slE scE))) "else-branch reads a dropped goal's variable"
        let outer = (readT `IS.difference` (prodT `IS.union` prodC)) `IS.union` (readE `IS.difference` prodE)
                    `IS.union` (readC `IS.difference` prodC)
        return (NR (g : filter (`notElem` local) (nrConsumed nrT ++ nrConsumed nrE)) outer
                   (nrFresh nrT ++ nrFresh nrE) (nrDisp nrT ++ nrDisp nrE))
      _ -> Left (h ++ "unknown rule")
  _ -> Left (here ++ "not a derivation node: " ++ take 100 (showTermQ node))
  where
    subjId (Var i _) = i
    subjId _ = -1

closurePrefixC :: [Term] -> ([Term], Bool)
closurePrefixC [] = ([], True)
closurePrefixC (c : cs) = case c of
  Comp "plop2_static" [l] | Right xs <- listOf l -> let (rest, ok) = closurePrefixC cs in (xs ++ rest, ok)
  Comp "plop2_chain_c" [l] | Right inner <- listOf l ->
    let (xs, ok) = closurePrefixC inner
    in if ok then let (rest, ok2) = closurePrefixC cs in (xs ++ rest, ok2) else (xs, False)
  _ -> ([], False)

interleaveC :: Term -> [Term] -> [Term]
interleaveC _ [] = []
interleaveC _ [x] = [x]
interleaveC s (x : xs) = x : s : interleaveC s xs

-- | A closure for one part of a concatenation.
checkClosure :: Cx -> String -> IS.IntSet -> Scope -> Bool -> Int -> Term -> Term -> Check (Term, NR)
checkClosure cx h srcVars sc textMode k part cl = case cl of
  Comp "cl" [Atom rule, p, clo, info] -> do
    ensure (p == part) (h ++ "closure for another part")
    case rule of
      "cl_static" -> do
        let elems = case (textMode, part) of
              (True, Atom a) -> Just [ Atom [c] | c <- a ]
              (True, Int x) -> Just [ Atom [c] | c <- show x ]
              _ -> groundList part
        case elems of
          Just xs -> ensure (clo == Comp "plop2_static" [mkList xs (Atom "[]")]) (h ++ "static part") >> return (clo, mempty)
          Nothing -> Left (h ++ "part is not static")
      "cl_value" -> do
        ensure (clo == Comp "plop2_value" [part]) (h ++ "value part")
        return (clo, mempty { nrNeeds = IS.intersection (termVarIds part) srcVars })
      "cl_spec" -> do
        w <- case part of
          Var i _ -> return i
          _ -> Left (h ++ "a spec part must be a variable")
        (ix, pg) <- case producerIn sc w of
          Just (ix, g) | g == info -> return (ix, g)
          _ -> Left (h ++ "the recorded goal is not the part's first producer")
        key <- maybe (Left (h ++ "producer not callable")) return (goalKey pg)
        ensure (M.member key (progPreds (cxSrc cx))) (h ++ "producer is not a user predicate")
        let pargs = goalArgs pg
        pos <- case [ i | (i, a) <- zip [0 ..] pargs, a == part ] of
          [q] -> return q
          _ -> Left (h ++ "the part is not exactly one argument of its producer")
        let usedAny = Set.unions [ cxUsed cx (Sp key pos jj) | jj <- [1 .. k] ]
            gnd = groundBefore sc ix
            others = [ (i, a) | (i, a) <- zip [0 ..] pargs, i /= pos ]
        forM_ [1 .. k] $ \jj -> ensure (Set.member (Sp key pos jj) (cxSpecs cx)) (h ++ "missing program for position " ++ show jj)
        case clo of
          Comp nm cargs | nm == dName key pos k && length cargs == length others -> do
            frs <- forM (zip others cargs) $ \((i, a), b) ->
              if Set.member i usedAny then do
                ensure (a == b) (h ++ "an argument the callee reads is not passed")
                ensure (IS.isSubsetOf (termVarIds a) gnd) (h ++ "an argument the callee reads is not ground at the call")
                return []
              else do
                ensure (isFreshIn srcVars b) (h ++ "an unused argument is not a fresh variable")
                return [ i' | Var i' _ <- [b] ]
            return (clo, NR [pg] (IS.intersection (IS.unions (map termVarIds cargs)) srcVars) (concat frs) [(key, pos, k)])
          _ -> Left (h ++ "dispatcher closure")
      "cl_chain" -> do
        w <- case part of
          Var i _ -> return i
          _ -> Left (h ++ "a chain part must be a variable")
        (pg, subCls) <- case info of
          Comp "chain" [pg, l] -> (,) pg <$> listOf l
          _ -> Left (h ++ "chain info")
        ix <- case producerIn sc w of
          Just (ix, g) | g == pg -> return ix
          _ -> Left (h ++ "the recorded goal is not the part's first producer")
        (innerText, innerParts) <- case pg of
          Comp "append" [a, b, Var x _] | x == w -> return (False, [a, b])
          Comp f [a, b, Var x _] | x == w, f `elem` ["atom_concat", "string_concat"] -> return (True, [a, b])
          Comp "atomic_list_concat" [l, Var x _] | x == w -> (,) True <$> listOf l
          Comp "atomic_list_concat" [l, sp, Var x _] | x == w -> (\ps -> (True, interleaveC sp ps)) <$> listOf l
          _ -> Left (h ++ "producer is not a concatenation")
        ensure (length subCls == length innerParts) (h ++ "one closure per inner part")
        let sc' = sc { scGoals = take (ix - 1) (scGoals sc) }
        inner <- forM (zip innerParts subCls) $ \(ip, c) -> checkClosure cx h srcVars sc' innerText k ip c
        ensure (clo == Comp "plop2_chain_c" [mkList [ c | (c, _) <- inner ] (Atom "[]")]) (h ++ "nested chain")
        let nr = mconcat (map snd inner)
        return (clo, nr { nrConsumed = pg : nrConsumed nr })
      _ -> Left (h ++ "unknown closure rule")
  _ -> Left (h ++ "bad closure")
  where
    groundList (Atom "[]") = Just []
    groundList (Comp "." [x, tl]) | IS.null (termVarIds x) = (x :) <$> groundList tl
    groundList _ = Nothing

-- ---------------------------------------------------------------------------
-- Formula clauses: exact on the domain by exhaustive evaluation

checkFormula :: Program -> Term -> Check Clause
checkFormula generated s = case s of
  Comp "formula_step" [st, Int lo, Int hi, Int d, clT] -> do
    sp@(Sp (_, n) j _) <- spOf st
    cl <- asClause clT
    let prog = withPrelude generated
        name = spName sp
    ensure (goalKey (clHead cl) == Just (name, n)) "formula_step: wrong head"
    -- the formula clause and the sliced program agree on every domain point
    forM_ [lo .. hi] $ \x -> do
      let argsF = [ if i == j then Var 0 "C" else if i == fromIntegral d then Int x else Var (i + 10) "_" | i <- [0 .. n - 1] ]
          argsR = [ if i == j then Var 0 "R" else if i == fromIntegral d then Int x else Var (i + 10) "_" | i <- [0 .. n - 1] ]
          viaFormula = firstOf prog (Comp name argsF) (Var 0 "C")
          viaSlice = firstOf prog (Comp (name ++ "__r") argsR) (Var 0 "R")
      case (viaFormula, viaSlice) of
        (Right (Just a), Right (Just (Comp "c" [b]))) | a == b -> return ()
        (Right Nothing, Right (Just (Atom "none"))) -> return ()
        _ -> Left ("formula_step for " ++ name ++ ": the formula and the sliced program differ at " ++ show x)
    return cl
  _ -> Left "bad formula_step"
  where
    firstOf prog g v = go (runGoal defaultOptions prog g 100)
      where
        go [] = Right Nothing
        go (Out _ : r) = go r
        go (Err e : _) = Left e
        go (Ans st : _) = Right (Just (resolve st v))

-- ---------------------------------------------------------------------------
-- Input-character facts: symbolic evaluation on character variables

checkInputChars :: Program -> Term -> Check Clause
checkInputChars generated s = case s of
  Comp "input_chars_step" [st, clT] -> do
    sp@(Sp (_, n) j _) <- spOf st
    cl <- asClause clT
    let name = spName sp
        hargs = goalArgs (clHead cl)
        prog = withPrelude generated
    ensure (goalKey (clHead cl) == Just (name ++ "__in", n)) "input_chars_step: wrong head"
    case clBody cl of
      Atom "true" -> do
        let inputVars = IS.unions [ termVarIds a | (i, a) <- zip [0 ..] hargs, i /= j ]
            rv = Var 999999 "R"
            goal = Comp (name ++ "__r") [ if i == j then rv else a | (i, a) <- zip [0 ..] hargs ]
            -- a watched run: any built-in that inspects an input variable is an
            -- error, so the answer holds for every input of this shape
            stream = take 3 (runGoal defaultOptions { optWatch = IS.toList inputVars } prog goal 1000000)
        case [ st' | Ans st' <- stream ] of
          [st'] | null [ e | Err e <- stream ] -> do
            let ws = [ walk st' (Var v "") | v <- IS.toList inputVars ]
                distinctVars = all isVar ws && length (Set.fromList [ i | Var i _ <- ws ]) == length ws
                rename t = case t of
                  Var w _ -> head ([ Var v "" | v <- IS.toList inputVars, walk st' (Var v "") == Var w "" ] ++ [t])
                  Comp f as -> Comp f (map rename as)
                  x -> x
            ensure distinctVars ("input_chars_step for " ++ name ++ ": the run constrains the input characters")
            ensure (rename (resolve st' rv) == Comp "c" [hargs !! j])
                   ("input_chars_step for " ++ name ++ ": the symbolic run gives another character")
            return cl
          _ -> Left ("input_chars_step for " ++ name ++ ": the symbolic run does not give exactly one answer")
      _ -> do
        -- a wrapper over the sliced program
        ensure (clBody cl == Comp (name ++ "__r") [ if i == j then Comp "c" [hargs !! j] else a | (i, a) <- zip [0 ..] hargs ])
               ("input_chars_step for " ++ name ++ ": wrapper")
        return cl
  _ -> Left "bad input_chars_step"
