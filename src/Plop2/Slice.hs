-- | Per-character demand slicing.
--
-- For an algorithm @p(In..., Out)@ and a position @k@, plop2 writes a
-- separate program @p__chark(In..., C)@ that computes only the k-th
-- character (element) of @Out@.  Each position is developed on its own:
--
--   * the demand "element k of V" is pushed back to the goal that produces V;
--   * a call @q(..., V)@ becomes a call of q's own specialised program for
--     that position (@q__charj@), and q's other arguments are passed only if
--     that program uses them (otherwise they are @_@);
--   * list and text builders are unrolled for the one position:
--     @append/3@, @atom_concat/3@, @atomic_list_concat/2,3@, @atom_chars/2@,
--     @atom_codes/2@, @number_codes/2@, @reverse/2@, @maplist/3@, and
--     literal lists such as @[H|T]@ or @"abc"@;
--   * only the goals that bind variables the character needs are kept
--     (plus guards and input matches, which select clauses); every goal
--     that only builds other characters is dropped, so the program has no
--     variables for the other data.
--
-- Recursion over the output becomes a chain of distinct programs (char3
-- calls char2 on the tail, which calls char1), not one shared loop.
--
-- Assumption: a dropped goal would have succeeded (it only built data for
-- other characters).  plop2's check compares every position with the
-- original algorithm's output.
module Plop2.Slice
  ( Spec(..)
  , specName
  , SliceResult(..)
  , slicePositions
  , helperSource
  ) where

import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Builtins (effectKeys)
import Detlog2.Parser
import Detlog2.Term

-- | A specialised program: predicate, output argument (0-based), position.
data Spec = Spec { spKey :: PredKey, spOut :: Int, spK :: Int }
  deriving (Eq, Ord, Show)

specName :: Spec -> String
specName (Spec (f, n) j k)
  | j == n - 1 = f ++ "__char" ++ show k
  | otherwise = f ++ "__a" ++ show (j + 1) ++ "_char" ++ show k

data SliceResult = SliceResult
  { srClauses :: M.Map Spec [Clause]
  , srUsed :: M.Map Spec (Set.Set Int)     -- ^ input parameters each program reads
  , srNotes :: [String]
  }

-- ---------------------------------------------------------------------------
-- Generation monad

data GS = GS
  { gsNext :: !Int
  , gsRequests :: Set.Set Spec
  , gsNotes :: [String]
  }

newtype G a = G { runG :: GS -> (a, GS) }

instance Functor G where
  fmap f (G g) = G $ \s -> let (a, s') = g s in (f a, s')
instance Applicative G where
  pure a = G $ \s -> (a, s)
  G f <*> G g = G $ \s -> let (h, s1) = f s
                              (a, s2) = g s1
                          in (h a, s2)
instance Monad G where
  G g >>= k = G $ \s -> let (a, s1) = g s in runG (k a) s1

fresh :: String -> G Term
fresh n = G $ \s -> (Var (gsNext s) n, s { gsNext = gsNext s + 1 })

request :: Spec -> G ()
request sp = G $ \s -> ((), s { gsRequests = Set.insert sp (gsRequests s) })

note :: String -> G ()
note n = G $ \s -> ((), s { gsNotes = n : gsNotes s })

data Env = Env
  { envProg :: Program
  , envUsed :: M.Map Spec (Set.Set Int)
  , envBase :: Int            -- ^ first id of generated variables in this clause
  }

-- ---------------------------------------------------------------------------
-- Entry point

-- | Slice the output argument of a predicate for positions 1..n.  The
-- program must be cut-free (run detlog2's cut elimination first).
slicePositions :: Program -> PredKey -> Int -> Int -> SliceResult
slicePositions prog key outArg n = loop M.empty 0
  where
    roots = Set.fromList [ Spec key outArg k | k <- [1 .. n] ]
    loop used iter =
      let (clauses, used', notes) = generateAll used
      in if used' == used || iter > (50 :: Int)
           then SliceResult clauses used' (reverse notes)
           else loop used' (iter + 1)
    generateAll used = go roots Set.empty M.empty used []
      where
        go pending done acc usedAcc notes
          | Set.null pending = (acc, usedAcc, notes)
          | otherwise =
              let (sp, rest) = Set.deleteFindMin pending
                  (cls, usedSp, reqs, ns) = sliceSpec (Env prog used 0) sp
                  done' = Set.insert sp done
                  newReqs = Set.filter (`Set.notMember` done') reqs `Set.difference` rest
              in go (rest `Set.union` newReqs) done' (M.insert sp cls acc)
                    (M.insert sp usedSp usedAcc) (notes ++ ns)

-- | All clauses of one specialised program.
sliceSpec :: Env -> Spec -> ([Clause], Set.Set Int, Set.Set Spec, [String])
sliceSpec env sp@(Spec key j k) =
  let cls = M.findWithDefault [] key (progPreds (envProg env))
      results = [ sliceClause env sp c | c <- cls ]
      kept = [ (c, u) | (Just (c, u), _, _) <- results ]
      used = Set.unions (map snd kept)
      reqs = Set.unions [ r | (_, r, _) <- results ]
      notes = concat [ ns | (_, _, ns) <- results ]
  in if M.member key (progPreds (envProg env))
       then ([ c | (c, _) <- kept ], used, reqs, notes)
       else ([], Set.empty, Set.empty, ["no clauses for " ++ fst key ++ "/" ++ show (snd key)])
  where _ = (j, k)

sliceClause :: Env -> Spec -> Clause -> (Maybe (Clause, Set.Set Int), Set.Set Spec, [String])
sliceClause env0 sp@(Spec _ j k) (Clause h body nv) =
  let env = env0 { envBase = nv }
      args = goalArgs h
      outT = args !! j
      inputs = [ a | (i, a) <- zip [0 ..] args, i /= j ]
      bound = IS.unions (map termVarIds inputs)
      gs = conjList body
      gen = do
        c <- fresh "C"
        (e, needs) <- termExpr env bound gs outT k c
        let (kept, _) = closeOver env bound gs needs
        return (c, e, kept)
      ((c, e, kept), st) = runG gen (GS (nv + 1) Set.empty [])
      newBody = mkConj (kept ++ [e])
      newArgs = [ if i == j then c else a | (i, a) <- zip [0 ..] args ]
      newHead = Comp (specName sp) newArgs
      bodyVars = termVarIds newBody
      headCounts = M.fromListWith (+) [ (v, 1 :: Int) | a <- args, Var v _ <- termVarsOrdered' a ]
      used = Set.fromList
        [ i | (i, a) <- zip [0 ..] args, i /= j
            , not (isVar a)
              || not (IS.null (IS.intersection (termVarIds a) bodyVars))
              || any (\v -> M.findWithDefault 0 v headCounts > 1) (IS.toList (termVarIds a))
              || not (IS.null (IS.intersection (termVarIds a) (termVarIds outT))) ]
      clause = Clause newHead newBody (gsNext st)
  in if e == Atom "fail"
       then (Nothing, gsRequests st, reverse (gsNotes st))
       else (Just (clause, used), gsRequests st, reverse (gsNotes st))
  where
    termVarsOrdered' t = [ x | x@(Var _ _) <- allVarOccurrences t ]

allVarOccurrences :: Term -> [Term]
allVarOccurrences t@(Var _ _) = [t]
allVarOccurrences (Comp _ as) = concatMap allVarOccurrences as
allVarOccurrences _ = []

-- ---------------------------------------------------------------------------
-- Producers

-- | Variables each goal binds first (given the variables bound before).
withProduced :: IS.IntSet -> [Term] -> [(Term, IS.IntSet)]
withProduced bound = go bound
  where
    go _ [] = []
    go seen (g : gs) =
      let vs = termVarIds g
          prod = vs `IS.difference` seen
      in (g, prod) : go (seen `IS.union` vs) gs

producedIn :: IS.IntSet -> [Term] -> IS.IntSet
producedIn bound gs = IS.unions (map snd (withProduced bound gs))

-- | The goal that binds V first, with the goals before it.
findProducer :: IS.IntSet -> [Term] -> Int -> Maybe (Term, [Term])
findProducer bound gs v =
  case [ (i, g) | (i, (g, prod)) <- zip [0 ..] (withProduced bound gs), IS.member v prod ] of
    ((i, g) : _) -> Just (g, take i gs)
    [] -> Nothing

-- | Expression for "element k of term T", into R.  Returns the goal and the
-- variables it needs bound.
termExpr :: Env -> IS.IntSet -> [Term] -> Term -> Int -> Term -> G (Term, IS.IntSet)
termExpr env bound prefix t k r = case t of
  Var v _ -> charExpr env bound prefix v t k r
  Comp "." [h, tl]
    | k == 1 -> return (eq r h, localVars env h)
    | otherwise -> termExpr env bound prefix tl (k - 1) r
  Atom "[]" -> return (Atom "fail", IS.empty)
  Atom a -> return (textChar a)
  Int i -> return (textChar (show i))
  _ -> do
    note ("element " ++ show k ++ " of a non-list term is taken with plop2_nth_char/3")
    return (Comp "plop2_nth_char" [Int (fromIntegral k), t, r], localVars env t)
  where
    textChar s
      | k <= length s = (eq r (Atom [s !! (k - 1)]), IS.empty)
      | otherwise = (Atom "fail", IS.empty)

-- | Expression for "element k of variable V".
charExpr :: Env -> IS.IntSet -> [Term] -> Int -> Term -> Int -> Term -> G (Term, IS.IntSet)
charExpr env bound prefix v vt k r = case findProducer bound prefix v of
  Nothing
    | IS.member v bound -> return (nthChar vt, IS.singleton v)
    | otherwise -> return (Atom "fail", IS.empty)
  Just (g, before)
    -- V = W where W is also new here: the real producer of W comes later
    | Just w <- aliasOf g, not (IS.member w (bound `IS.union` IS.unions (map termVarIds before))) ->
        let prefix' = before ++ drop (length before + 1) prefix
            wt = head [ x | x@(Var i _) <- goalArgs g, i == w ]
        in charExpr env bound prefix' w wt k r
    | otherwise -> producerExpr env bound before g v vt k r
  where
    aliasOf g = case g of
      Comp "=" [Var a _, Var b _] | a == v && b /= v -> Just b
                                  | b == v && a /= v -> Just a
      _ -> Nothing
    nthChar x = Comp "plop2_nth_char" [Int (fromIntegral k), x, r]

producerExpr :: Env -> IS.IntSet -> [Term] -> Term -> Int -> Term -> Int -> Term -> G (Term, IS.IntSet)
producerExpr env bound before g v vt k r = case g of
  Comp "=" [x, t] | isV x -> termExpr env bound before t k r
  Comp "=" [t, x] | isV x -> termExpr env bound before t k r
  Comp ";" [Comp "->" [c, t], e] -> branches "ite" c t e
  Comp "->" [c, t] -> branches "ite" c t (Atom "fail")
  Comp "if_commit" [c, t, e] -> branches "if_commit" c t e
  Comp ";" [a, b] -> do
    (ga, na) <- branch before (conjList a)
    (gb, nb) <- branch before (conjList b)
    return (Comp ";" [ga, gb], na `IS.union` nb)
  Comp f [a, b, x] | isV x, f `elem` ["append"] -> chain ListMode [a, b] k r
  Comp f [a, b, x] | isV x, f `elem` ["atom_concat", "string_concat"] -> chain TextMode [a, b] k r
  Comp "atomic_list_concat" [l, x] | isV x, Just parts <- staticList l -> chain TextMode parts k r
  Comp "atomic_list_concat" [l, sep, x] | isV x, Just parts <- staticList l ->
    chain TextMode (interleave sep parts) k r
  Comp f [a, x] | isV x, f `elem` ["atom_chars", "string_chars", "atom_string", "string_to_atom"] -> anyExpr a k r
  Comp f [x, l] | isV x, f `elem` ["atom_chars", "string_chars"] -> anyExpr l k r
  Comp "atom_codes" [a, x] | isV x -> do
    r0 <- fresh "Ch"
    (e, n) <- anyExpr a k r0
    return (mkConj [e, Comp "char_code" [r0, r]], n)
  Comp "atom_codes" [x, l] | isV x -> do
    r0 <- fresh "Code"
    (e, n) <- anyExpr l k r0
    return (mkConj [e, Comp "char_code" [r, r0]], n)
  Comp "number_codes" [num, x] | isV x -> do
    r0 <- fresh "Ch"
    return (mkConj [nth num r0, Comp "char_code" [r0, r]], localVars env num)
  Comp "number_chars" [num, x] | isV x -> return (nth num r, localVars env num)
  Comp "atom_number" [x, num] | isV x -> return (nth num r, localVars env num)
  Comp "reverse" [l, x] | isV x -> do
    len <- fresh "Len"
    i <- fresh "I"
    note ("element " ++ show k ++ " of reverse/2 needs the whole input list")
    return ( mkConj [ Comp "length" [l, len]
                    , Comp "is" [i, Comp "+" [Comp "-" [len, Int (fromIntegral k)], Int 1]]
                    , Comp ">=" [i, Int 1]
                    , Comp "nth1" [i, l, r] ]
           , localVars env l )
  Comp "maplist" [f, l, x] | isV x, not (isVar f), isCallable f -> do
    xv <- fresh "X"
    (e, n) <- anyExpr l k xv
    case addArgs f [xv, r] of
      Just call -> return (mkConj [e, call], n `IS.union` localVars env f)
      Nothing -> fallback
  _ -> case goalKey g of
    Just key | M.member key (progPreds (envProg env))
             , [pos] <- [ i | (i, a) <- zip [0 ..] (goalArgs g), isV a ]
             , not (IS.member v (IS.unions [ termVarIds a | (i, a) <- zip [0 :: Int ..] (goalArgs g), i /= pos ])) -> do
        let sp = Spec key pos k
            used = M.findWithDefault Set.empty sp (envUsed env)
            args' = [ if i == pos then r else if Set.member i used then a else Atom "_"
                    | (i, a) <- zip [0 ..] (goalArgs g) ]
        request sp
        args'' <- mapM (\a -> if a == Atom "_" then fresh "_" else return a) args'
        let needs = IS.unions [ localVars env a | (i, a) <- zip [0 ..] args'', i /= pos ]
        return (Comp (specName sp) args'', needs)
    _ -> fallback
  where
    isV x = case x of
      Var i _ -> i == v
      _ -> False
    nth x out = Comp "plop2_nth_char" [Int (fromIntegral k), x, out]
    fallback = do
      note ("element " ++ show k ++ ": the producer of a variable is kept in full: " ++ take 60 (show (goalKey g)))
      return (Comp "plop2_nth_char" [Int (fromIntegral k), vt, r], IS.singleton v)
    anyExpr t kk out = case t of
      Var i _ -> charExpr env bound before i t kk out
      _ -> termExpr env bound before t kk out
    -- A producing if-then-else: slice each branch separately.
    branches kind c t e = do
      let cs = conjList c
          ts = conjList t
          es = conjList e
          boundBefore = bound `IS.union` producedIn bound before
      (eT, nT) <- charExpr env bound (before ++ cs ++ ts) v vt k r
      let (keptT, nT') = closeOver env (boundBefore `IS.union` producedIn boundBefore cs) ts nT
          (keptC, nC) = closeOver env boundBefore cs nT'
      (eE, nE) <- charExpr env bound (before ++ es) v vt k r
      let (keptE, nE') = closeOver env boundBefore es nE
          cond = mkConj keptC
          thenG = mkConj (keptT ++ [eT])
          elseG = mkConj (keptE ++ [eE])
          goal = case kind of
            "if_commit" -> Comp "if_commit" [cond, thenG, elseG]
            _ -> Comp ";" [Comp "->" [cond, thenG], elseG]
      return (goal, nC `IS.union` nE')
    branch bef bs = do
      (e1, n1) <- charExpr env bound (bef ++ bs) v vt k r
      let boundBefore = bound `IS.union` producedIn bound bef
          (kept, n1') = closeOver env boundBefore bs n1
      return (mkConj (kept ++ [e1]), n1')
    -- Unroll a list or text concatenation for this one position.
    chain _ [] _ _ = return (Atom "fail", IS.empty)
    chain mode (p : ps) kk out = case staticElems mode p of
      Just xs
        | kk <= length xs -> return (eq out (xs !! (kk - 1)), IS.empty)
        | otherwise -> chain mode ps (kk - length xs) out
      Nothing -> do
        (ek, nk) <- anyExpr p kk out
        case ek of
          Comp "=" [_, _] -> return (ek, nk)     -- cannot fail: no shorter cases
          _ -> chainAlts mode p ps kk out ek nk
    chainAlts mode p ps kk out ek nk = do
        alts <- mapM (\jj -> do
                        probe <- fresh "_"
                        (tj, nj) <- if jj == 0 then return (Atom "true", IS.empty) else anyExpr p jj probe
                        (rj, mj) <- chain mode ps (kk - jj) out
                        return (tj, rj, nj `IS.union` mj))
                     [kk - 1, kk - 2 .. 0]
        let build [] = Atom "fail"
            build [(Atom "true", rj, _)] = rj
            -- a probe that cannot fail (a fixed character): later cases are unreachable
            build ((Comp "=" [_, _], rj, _) : _) = rj
            build ((tj, rj, _) : more) = Comp ";" [Comp "->" [tj, rj], build more]
            goal = case build alts of
              Atom "fail" -> ek
              rest -> Comp ";" [Comp "->" [ek, Atom "true"], rest]
        return (goal, nk `IS.union` IS.unions [ n | (_, _, n) <- alts ])

data Mode = ListMode | TextMode

staticElems :: Mode -> Term -> Maybe [Term]
staticElems ListMode t = groundList t
  where
    groundList (Atom "[]") = Just []
    groundList (Comp "." [h, tl]) | IS.null (termVarIds h) = (h :) <$> groundList tl
    groundList _ = Nothing
staticElems TextMode t = case t of
  Atom a -> Just [ Atom [c] | c <- a ]
  Int i -> Just [ Atom [c] | c <- show i ]
  _ -> staticElems ListMode t

staticList :: Term -> Maybe [Term]
staticList (Atom "[]") = Just []
staticList (Comp "." [h, t]) = (h :) <$> staticList t
staticList _ = Nothing

interleave :: Term -> [Term] -> [Term]
interleave _ [] = []
interleave _ [x] = [x]
interleave s (x : xs) = x : s : interleave s xs

eq :: Term -> Term -> Term
eq a b = Comp "=" [a, b]

-- | Source variables of a term (generated variables excluded).
localVars :: Env -> Term -> IS.IntSet
localVars env t = IS.filter (< envBase env) (termVarIds t)

-- ---------------------------------------------------------------------------
-- Keeping only what is needed

-- | Keep the goals that bind demanded variables, plus input matches and
-- guards that select clauses.  Returns the kept goals and the demanded
-- variables that must come from outside these goals.
closeOver :: Env -> IS.IntSet -> [Term] -> IS.IntSet -> ([Term], IS.IntSet)
closeOver env bound gs demand0 =
  let annotated = zip [0 :: Int ..] (withProduced bound gs)
      -- pass 1: producers of demanded variables, and matches on bound inputs
      pass1 = foldr step (Set.empty, demand0) annotated
      step (i, (g, prod)) (keep, d)
        | not (IS.null (IS.intersection prod d)) = (Set.insert i keep, d `IS.union` localVars env g)
        | isMatch g prod = (Set.insert i keep, d `IS.union` (localVars env g `IS.difference` prod))
        | isGuard g prod && IS.isSubsetOf (termVarIds g) bound = (Set.insert i keep, d `IS.union` localVars env g)
        | otherwise = (keep, d)
      (keep1, d1) = pass1
      keptVars = IS.unions [ termVarIds g | (i, (g, _)) <- annotated, Set.member i keep1 ]
      available = bound `IS.union` d1 `IS.union` keptVars
      -- pass 2: guards over variables that are available anyway
      keep2 = keep1 `Set.union` Set.fromList
        [ i | (i, (g, prod)) <- annotated, isGuard g prod
            , IS.isSubsetOf (termVarIds g) available ]
      d2 = d1 `IS.union` IS.unions [ localVars env g | (i, (g, _)) <- annotated, Set.member i keep2 ]
      kept = [ g | (i, (g, _)) <- annotated, Set.member i keep2 ]
      prodAll = IS.unions (map (snd . snd) annotated)
  in (kept, d2 `IS.difference` prodAll)
  where
    isMatch g prod = case g of
      Comp "=" [a, b] -> (boundVar a prod && not (isVar b)) || (boundVar b prod && not (isVar a))
      _ -> False
    boundVar x prod = case x of
      Var i _ -> not (IS.member i prod)
      _ -> False
    isGuard g prod = IS.null prod && not (isEffect g)
    isEffect g = maybe False (`elem` effectKeys) (goalKey g)

-- ---------------------------------------------------------------------------
-- Helpers written into every generated file (cut-free).

helperSource :: String
helperSource = unlines
  [ "% plop2_nth_char(+K, +T, -C): element K of a list, or character K of an atom or integer."
  , "plop2_nth_char(K, T, C) :-"
  , "    (   integer(T)"
  , "    ->  plop2_int_char(K, T, C)"
  , "    ;   atom(T)"
  , "    ->  B is K - 1, sub_atom(T, B, 1, _, C)"
  , "    ;   nth1(K, T, C)"
  , "    )."
  , "% Character K of an integer by formula: digit = (N // 10^(D-K)) mod 10."
  , "plop2_int_char(K, N, C) :-"
  , "    (   N < 0"
  , "    ->  (   K =:= 1 -> C = '-' ; K1 is K - 1, M is -N, plop2_int_char(K1, M, C) )"
  , "    ;   plop2_ndigits(N, D), K >= 1, K =< D,"
  , "        Digit is (N // 10 ^ (D - K)) mod 10,"
  , "        Code is 0'0 + Digit, char_code(C, Code)"
  , "    )."
  , "plop2_ndigits(N, D) :- ( N < 10 -> D = 1 ; M is N // 10, plop2_ndigits(M, D0), D is D0 + 1 )."
  ]
