-- | Per-character demand slicing with proofs.
--
-- For an algorithm @p(In..., Out)@ and a position @k@, plop2 writes a
-- separate program that computes only element k of @Out@:
--
-- > p__chark(In..., C)        C is element k of Out (fails if there is none)
-- > p__chark__r(In..., R)     R = c(C), or R = none if Out has no element k
-- > p__chark__alt(In..., R)   one clause per source clause (first answer wins)
--
-- Each clause of @p__chark__alt@ keeps a subsequence of the source clause's
-- goals and ends with an /element expression/ for element k of the output:
--
--   * a goal is kept if it binds a variable the element needs, or if it may
--     fail (a guard or an input match that selects the clause);
--   * a goal that only builds other data is dropped only with a totality
--     certificate: it always succeeds, exactly once.  A goal without a
--     certificate is kept;
--   * the goal that produces the output (or a part of it) is /consumed/ by
--     the element expression: a call @q(..., V)@ becomes a call of q's own
--     program for that position, @q__charj__r@; @append/3@ and the text
--     builders become @plop2_chain/3@ over the parts; literal lists such as
--     @[H|T]@ or @"abc"@ are read directly.
--
-- Every clause is recorded as a proof step with its derivation; see
-- "Plop2.Proof" and docs/proof_rules.md.
module Plop2.Slice
  ( Spec(..)
  , specName
  , altName
  , rName
  , dispName
  , SliceResult(..)
  , slicePositions
  , helperSource
  , specTerm
  ) where

import qualified Data.IntSet as IS
import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Parser
import Detlog2.Term

-- | A specialised program: predicate, output argument (0-based), position.
data Spec = Spec { spKey :: PredKey, spOut :: Int, spK :: Int }
  deriving (Eq, Ord, Show)

specName :: Spec -> String
specName (Spec (f, n) j k)
  | j == n - 1 = f ++ "__char" ++ show k
  | otherwise = f ++ "__a" ++ show (j + 1) ++ "_char" ++ show k

altName, rName :: Spec -> String
altName sp = specName sp ++ "__alt"
rName sp = specName sp ++ "__r"

-- | The dispatcher for positions 1..k of one output argument.
dispName :: PredKey -> Int -> Int -> String
dispName (f, _) j k = f ++ "__a" ++ show (j + 1) ++ "_upto" ++ show k ++ "_r"

specTerm :: Spec -> Term
specTerm (Spec (f, n) j k) =
  Comp "spec" [Comp "/" [Atom f, Int (fromIntegral n)], Int (fromIntegral j), Int (fromIntegral k)]

data SliceResult = SliceResult
  { srClauses :: M.Map Spec [Clause]          -- ^ __alt clauses
  , srUsed :: M.Map Spec (Set.Set Int)        -- ^ input parameters each program reads
  , srDisp :: Set.Set (PredKey, Int, Int)     -- ^ dispatchers needed
  , srSteps :: [Term]                         -- ^ one slice_step per __alt clause
  , srNotes :: [String]
  }

-- ---------------------------------------------------------------------------
-- Generation monad

data GS = GS
  { gsNext :: !Int
  , gsRequests :: Set.Set Spec
  , gsDisp :: Set.Set (PredKey, Int, Int)
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

requestDisp :: (PredKey, Int, Int) -> G ()
requestDisp d = G $ \s -> ((), s { gsDisp = Set.insert d (gsDisp s) })

note :: String -> G ()
note n = G $ \s -> ((), s { gsNotes = n : gsNotes s })

data Env = Env
  { envProg :: Program
  , envUsed :: M.Map Spec (Set.Set Int)
  , envBase :: Int            -- ^ first id of generated variables in this clause
  , envFull :: IS.IntSet      -- ^ variables to read from their full value
  }

-- | Where an element expression is built: the goals visible before it, and
-- the variables bound and ground before those goals.
data Ctx = Ctx
  { cxVisible :: [Term]
  , cxBound :: IS.IntSet
  , cxGround :: IS.IntSet
  }

-- | An element expression: its derivation node, the variables it reads
-- (which kept goals or inputs must bind), the goals it consumed, and
-- variables of consumed goals that kept goals also read (conflicts).
data EX = EX { exNode :: Term, exNeeds :: IS.IntSet, exConsumed :: [Term], exConflicts :: IS.IntSet }

-- | e(Rule, Subject, K, R, Goal, Subs, Info)
enode :: String -> Term -> Int -> Term -> Term -> [Term] -> Term -> Term
enode rule subj k r goal subs info =
  Comp "e" [Atom rule, subj, Int (fromIntegral k), r, goal, mkList subs (Atom "[]"), info]

goalOf :: Term -> Term
goalOf (Comp "e" [_, _, _, _, g, _, _]) = g
goalOf (Comp "cl" [_, _, c, _]) = c
goalOf t = t

-- ---------------------------------------------------------------------------
-- Entry point

slicePositions :: Program -> PredKey -> Int -> Int -> SliceResult
slicePositions prog key outArg n = loop M.empty (0 :: Int)
  where
    roots = Set.fromList [ Spec key outArg k | k <- [1 .. n] ]
    loop used iter =
      let r = generateAll used
      in if srUsed r == used || iter > 50 then r else loop (srUsed r) (iter + 1)
    generateAll used = go roots Set.empty M.empty M.empty Set.empty [] []
      where
        go pending done acc usedAcc disp steps notes
          | Set.null pending = SliceResult acc usedAcc disp steps notes
          | otherwise =
              let (sp, rest) = Set.deleteFindMin pending
                  (cls, usedSp, reqs, ds, st, ns) = sliceSpec prog used sp
                  done' = Set.insert sp done
                  newReqs = Set.filter (`Set.notMember` done') reqs `Set.difference` rest
              in go (rest `Set.union` newReqs) done' (M.insert sp cls acc)
                    (M.insert sp usedSp usedAcc) (disp `Set.union` ds) (steps ++ st) (notes ++ ns)

sliceSpec :: Program -> M.Map Spec (Set.Set Int) -> Spec
          -> ([Clause], Set.Set Int, Set.Set Spec, Set.Set (PredKey, Int, Int), [Term], [String])
sliceSpec prog used sp@(Spec key _ _) =
  let cls = M.findWithDefault [] key (progPreds prog)
      results = [ sliceClause prog used sp i c | (i, c) <- zip [1 ..] cls ]
  in ( [ c | (c, _, _, _, _, _) <- results ]
     , Set.unions [ u | (_, u, _, _, _, _) <- results ]
     , Set.unions [ r | (_, _, r, _, _, _) <- results ]
     , Set.unions [ d | (_, _, _, d, _, _) <- results ]
     , [ s | (_, _, _, _, s, _) <- results ]
     , concat [ ns | (_, _, _, _, _, ns) <- results ] )

sliceClause :: Program -> M.Map Spec (Set.Set Int) -> Spec -> Int -> Clause
            -> (Clause, Set.Set Int, Set.Set Spec, Set.Set (PredKey, Int, Int), Term, [String])
sliceClause prog used sp@(Spec _ j k) i (Clause h body nv) = attempt IS.empty (0 :: Int)
  where
    args = goalArgs h
    outT = args !! j
    inputs = [ a | (ix, a) <- zip [0 ..] args, ix /= j ]
    bound0 = IS.unions (map termVarIds inputs)
    gs = conjList body
    attempt full iter =
      let env = Env prog used nv full
          gen = do
            r <- fresh "R"
            ex <- termExpr env (Ctx gs bound0 bound0) outT k r
            let sl = closeOver env bound0 bound0 gs (exNeeds ex) (exConsumed ex)
            return (r, ex, sl)
          ((r, ex, sl), st) = runG gen (GS (nv + 1) Set.empty Set.empty [])
          conflicts = exConflicts ex `IS.union` slConflicts sl
      in if not (IS.null conflicts) && iter < 20
           then attempt (full `IS.union` conflicts) (iter + 1)
           else finish r ex sl st
    finish r ex sl st =
      let kept = [ g | (ix, g) <- zip [1 ..] gs, ix `elem` slKept sl ]
          newBody = mkConj (kept ++ [goalOf (exNode ex)])
          newArgs = [ if ix == j then r else a | (ix, a) <- zip [0 ..] args ]
          newHead = Comp (altName sp) newArgs
          clause = Clause newHead newBody (gsNext st)
          step = Comp "slice_step"
                   [ specTerm sp, Int (fromIntegral i)
                   , Comp ":-" [h, body], Comp ":-" [newHead, newBody]
                   , sliceTerm sl, exNode ex ]
      in (clause, usedParams j clause, gsRequests st, gsDisp st, step, reverse (gsNotes st))

-- | The input positions a program clause reads: a non-variable head
-- argument (it selects the clause), or a variable that occurs elsewhere.
usedParams :: Int -> Clause -> Set.Set Int
usedParams j (Clause h b _) =
  let args = goalArgs h
      counts = M.fromListWith (+) [ (v, 1 :: Int) | Var v _ <- concatMap allVars (args ++ [b]) ]
  in Set.fromList [ ix | (ix, a) <- zip [0 ..] args, ix /= j
                       , not (isVar a) || any (\v -> M.findWithDefault 0 v counts > 1) (IS.toList (termVarIds a)) ]

allVars :: Term -> [Term]
allVars t@(Var _ _) = [t]
allVars (Comp _ as) = concatMap allVars as
allVars _ = []

-- ---------------------------------------------------------------------------
-- Groundness and first occurrences (inputs are ground)

-- | Variables ground after a goal, given those ground before it.  Only
-- modes whose outputs are certainly ground are used; user predicates add
-- nothing.
groundAfter :: IS.IntSet -> Term -> IS.IntSet
groundAfter gr g = case g of
  Comp "=" [a, b]
    | gnd a -> gr `IS.union` termVarIds b
    | gnd b -> gr `IS.union` termVarIds a
  Comp "is" [x, e] | gnd e -> gr `IS.union` termVarIds x
  Comp f as@(_ : _)
    | (f, length as) `elem` functional && all gnd (init as) -> gr `IS.union` termVarIds (last as)
    | (f, length as) `elem` reversible && gnd (last as) -> gr `IS.union` IS.unions (map termVarIds (init as))
  _ -> gr
  where
    gnd t = IS.isSubsetOf (termVarIds t) gr
    functional =
      [ ("atom_codes", 2), ("atom_chars", 2), ("number_codes", 2), ("number_chars", 2)
      , ("atom_length", 2), ("char_code", 2), ("upcase_atom", 2), ("downcase_atom", 2)
      , ("atomic_list_concat", 2), ("atomic_list_concat", 3), ("atom_concat", 3)
      , ("string_concat", 3), ("string_chars", 2), ("atom_string", 2)
      , ("append", 3), ("reverse", 2), ("length", 2), ("nth0", 3), ("nth1", 3)
      , ("last", 2), ("sum_list", 2), ("max_list", 2), ("min_list", 2), ("msort", 2), ("sort", 2)
      , ("succ", 2), ("plus", 3) ]
    reversible = [ ("atom_codes", 2), ("atom_chars", 2), ("char_code", 2), ("string_chars", 2) ]

withProduced :: IS.IntSet -> [Term] -> [(Term, IS.IntSet)]
withProduced bound = go bound
  where
    go _ [] = []
    go seen (g : gs) =
      let vs = termVarIds g
      in (g, vs `IS.difference` seen) : go (seen `IS.union` vs) gs

producedIn :: IS.IntSet -> [Term] -> IS.IntSet
producedIn bound gs = IS.unions (map snd (withProduced bound gs))

groundThrough :: IS.IntSet -> [Term] -> IS.IntSet
groundThrough = foldl' groundAfter

-- | The goal that binds V first, with the goals before and after it.
findProducer :: IS.IntSet -> [Term] -> Int -> Maybe (Term, [Term], [Term])
findProducer bound gs v =
  case [ (ix, g) | (ix, (g, prod)) <- zip [0 ..] (withProduced bound gs), IS.member v prod ] of
    ((ix, g) : _) -> Just (g, take ix gs, drop (ix + 1) gs)
    [] -> Nothing

-- ---------------------------------------------------------------------------
-- Element expressions

nthR :: Int -> Term -> Term -> Term
nthR k t r = Comp "plop2_nth_r" [Int (fromIntegral k), t, r]

cOf :: Term -> Term
cOf x = Comp "c" [x]

eq :: Term -> Term -> Term
eq a b = Comp "=" [a, b]

ite :: Term -> Term -> Term -> Term
ite c t e = Comp ";" [Comp "->" [c, t], e]

noneG :: Term -> Term
noneG r = eq r (Atom "none")

localVars :: Env -> Term -> IS.IntSet
localVars env t = IS.filter (< envBase env) (termVarIds t)

leaf :: String -> Term -> Int -> Term -> Term -> Term -> IS.IntSet -> EX
leaf rule subj k r goal info needs = EX (enode rule subj k r goal [] info) needs [] IS.empty

-- | Element k of a term.
termExpr :: Env -> Ctx -> Term -> Int -> Term -> G EX
termExpr env cx t k r = case t of
  Var v _ -> charExpr env cx v t k r
  Comp "." [h, tl]
    | k == 1 -> return (leaf "el_head" t k r (eq r (cOf h)) (Atom "none") (localVars env h))
    | otherwise -> do
        sub <- termExpr env cx tl (k - 1) r
        return sub { exNode = enode "el_tail" t k r (goalOf (exNode sub)) [exNode sub] (Atom "none") }
  Atom "[]" -> return (leaf "el_none" t k r (noneG r) (Atom "none") IS.empty)
  Atom a -> return (textConst a)
  Int x -> return (textConst (show x))
  _ -> return (leaf "el_nth" t k r (nthR k t r) (Atom "none") (localVars env t))
  where
    textConst s
      | k <= length s = leaf "el_const" t k r (eq r (cOf (Atom [s !! (k - 1)]))) (Atom "none") IS.empty
      | otherwise = leaf "el_none" t k r (noneG r) (Atom "none") IS.empty

-- | Element k of a variable: from its full value, or from its producer.
charExpr :: Env -> Ctx -> Int -> Term -> Int -> Term -> G EX
charExpr env cx v vt k r
  | IS.member v (envFull env) = return (leaf "el_nth" vt k r (nthR k vt r) (Atom "none") (IS.singleton v))
  | otherwise = case findProducer (cxBound cx) (cxVisible cx) v of
      Nothing
        | IS.member v (cxBound cx) -> return (leaf "el_nth" vt k r (nthR k vt r) (Atom "none") (IS.singleton v))
        | otherwise -> return (leaf "el_none" vt k r (noneG r) (Atom "none") IS.empty)
      Just (g, before, after)
        | Just (w, wt) <- aliasOf g before -> do
            -- V = W with W also new here: the real producer of W comes later
            sub <- charExpr env cx { cxVisible = before ++ after } w wt k r
            return sub { exNode = enode "el_alias" vt k r (goalOf (exNode sub)) [exNode sub] g
                       , exConsumed = g : exConsumed sub }
        | otherwise -> do
            ex <- producerExpr env cx before g v vt k r
            return ex { exConsumed = g : exConsumed ex }
  where
    aliasOf g before =
      let seen = cxBound cx `IS.union` IS.unions (map termVarIds before)
      in case g of
           Comp "=" [a@(Var x _), b@(Var y _)]
             | x == v && y /= v && not (IS.member y seen) -> Just (y, b)
             | y == v && x /= v && not (IS.member x seen) -> Just (x, a)
           _ -> Nothing

producerExpr :: Env -> Ctx -> [Term] -> Term -> Int -> Term -> Int -> Term -> G EX
producerExpr env cx before g v vt k r = case g of
  Comp "=" [x, t] | isV x -> via "el_unify" t
  Comp "=" [t, x] | isV x -> via "el_unify" t
  Comp ";" [Comp "->" [c, t], e] -> branches (Just c) t e
  Comp "->" [c, t] -> branches (Just c) t (Atom "fail")
  Comp "if_commit" [c, t, e] -> branches (Just c) t e
  Comp ";" [a, b] -> branches Nothing a b
  Comp "append" [a, b, x] | isV x -> chainOf ListMode [a, b]
  Comp f [a, b, x] | isV x, f `elem` ["atom_concat", "string_concat"] -> chainOf TextMode [a, b]
  Comp "atomic_list_concat" [l, x] | isV x, Just ps <- staticList l -> chainOf TextMode ps
  Comp "atomic_list_concat" [l, sep, x] | isV x, Just ps <- staticList l -> chainOf TextMode (interleave sep ps)
  Comp f [a, x] | isV x, f `elem` ["atom_chars", "string_chars", "atom_string"] -> via "el_same_text" a
  Comp f [x, l] | isV x, f `elem` ["atom_chars", "string_chars"] -> via "el_same_text" l
  Comp "atom_codes" [a, x] | isV x -> convert "el_codes_of_text" a True
  Comp "atom_codes" [x, l] | isV x -> convert "el_text_of_codes" l False
  Comp "number_codes" [num, x] | isV x -> do
    r0 <- fresh "R0"
    ch <- fresh "Ch"
    code <- fresh "Code"
    let goal = mkConj [ nthR k num r0
                      , ite (eq r0 (cOf ch)) (mkConj [Comp "char_code" [ch, code], eq r (cOf code)]) (noneG r) ]
    return (EX (enode "el_number_codes" vt k r goal [] g) (localVars env num) [] IS.empty)
  Comp "number_chars" [num, x] | isV x -> return (EX (enode "el_number_chars" vt k r (nthR k num r) [] g) (localVars env num) [] IS.empty)
  Comp "atom_number" [x, num] | isV x -> return (EX (enode "el_number_chars" vt k r (nthR k num r) [] g) (localVars env num) [] IS.empty)
  Comp "reverse" [l, x] | isV x -> do
    len <- fresh "Len"
    ix <- fresh "I"
    xv <- fresh "X"
    note ("element " ++ show k ++ " of reverse/2 needs the whole input list")
    let goal = mkConj [ Comp "length" [l, len]
                      , Comp "is" [ix, Comp "+" [Comp "-" [len, Int (fromIntegral k)], Int 1]]
                      , ite (Comp ">=" [ix, Int 1]) (mkConj [Comp "nth1" [ix, l, xv], eq r (cOf xv)]) (noneG r) ]
    return (EX (enode "el_reverse" vt k r goal [] g) (localVars env l) [] IS.empty)
  Comp "maplist" [f, l, x] | isV x, not (isVar f), isCallable f, Just call <- addArgs f [Var (-1) "X", Var (-2) "Y"] -> do
    r0 <- fresh "R0"
    xv <- fresh "X"
    yv <- fresh "Y"
    sub <- anyExpr l k r0
    let Just call' = addArgs f [xv, yv]
        _ = call
        goal = mkConj [ goalOf (exNode sub)
                      , ite (eq r0 (cOf xv)) (mkConj [call', eq r (cOf yv)]) (noneG r) ]
    return sub { exNode = enode "el_maplist" vt k r goal [exNode sub] g
               , exNeeds = exNeeds sub `IS.union` localVars env f }
  _ -> case userOutput g of
    Just (key, pos) | groundArgs key pos [k] -> do
      let sp = Spec key pos k
          used = M.findWithDefault Set.empty sp (envUsed env)
      args' <- sequence [ if ix == pos then return r else if Set.member ix used then return a else fresh "_"
                        | (ix, a) <- zip [0 ..] (goalArgs g) ]
      request sp
      let needs = IS.unions [ localVars env a | (ix, a) <- zip [0 ..] args', ix /= pos ]
      return (EX (enode "el_spec" vt k r (Comp (rName sp) args') [] g) needs [] IS.empty)
    _ -> fallback
  where
    isV x = case x of
      Var ix _ -> ix == v
      _ -> False
    -- a user predicate whose output argument is exactly V, and V nowhere else
    userOutput goal = case goalKey goal of
      Just key | M.member key (progPreds (envProg env))
               , [pos] <- [ ix | (ix, a) <- zip [0 ..] (goalArgs goal), isV a ]
               , not (IS.member v (IS.unions [ termVarIds a | (ix, a) <- zip [0 :: Int ..] (goalArgs goal), ix /= pos ])) ->
          Just (key, pos)
      _ -> Nothing
    groundBefore = groundThrough (cxGround cx) before
    -- the arguments a program reads must be ground where the call was
    groundArgs key pos ks =
      let used = Set.unions [ M.findWithDefault Set.empty (Spec key pos kk) (envUsed env) | kk <- ks ]
      in and [ IS.isSubsetOf (termVarIds a) groundBefore | (ix, a) <- zip [0 ..] (goalArgs g), ix /= pos, Set.member ix used ]
    cxBefore = cx { cxVisible = before }
    anyExpr t kk out = case t of
      Var ix _ -> charExpr env cxBefore ix t kk out
      _ -> termExpr env cxBefore t kk out
    via rule t = do
      sub <- anyExpr t k r
      return sub { exNode = enode rule vt k r (goalOf (exNode sub)) [exNode sub] g }
    -- character <-> code conversion of element k
    convert rule t fromText = do
      r0 <- fresh "R0"
      ch <- fresh "Ch"
      code <- fresh "Code"
      sub <- anyExpr t k r0
      let (test, res) = if fromText then (eq r0 (cOf ch), cOf code) else (eq r0 (cOf code), cOf ch)
          goal = mkConj [ goalOf (exNode sub)
                        , ite test (mkConj [Comp "char_code" [ch, code], eq r res]) (noneG r) ]
      return sub { exNode = enode rule vt k r goal [exNode sub] g }
    fallback = do
      note ("element " ++ show k ++ ": the producer of a variable is kept in full: " ++ take 60 (show (goalKey g)))
      return (EX (enode "el_nth" vt k r (nthR k vt r) [] (Atom "none")) (IS.singleton v) [] (IS.singleton v))
    -- A producing if-then-else or disjunction: slice each branch.
    branches mc t e = do
      let cs = maybe [] conjList mc
          ts = conjList t
          es = conjList e
          boundBefore = cxBound cx `IS.union` producedIn (cxBound cx) before
          groundB = groundThrough (cxGround cx) before
      exT <- charExpr env cx { cxVisible = before ++ cs ++ ts } v vt k r
      exE <- charExpr env cx { cxVisible = before ++ es } v vt k r
      let slT = closeOver env (boundBefore `IS.union` producedIn boundBefore cs) (groundThrough groundB cs) ts (exNeeds exT) (exConsumed exT)
          slC = closeOver env boundBefore groundB cs (slNeeds slT) (exConsumed exT)
          slE = closeOver env boundBefore groundB es (exNeeds exE) (exConsumed exE)
          pick sl xs = [ x | (ix, x) <- zip [1 ..] xs, ix `elem` slKept sl ]
          thenG = mkConj (pick slT ts ++ [goalOf (exNode exT)])
          elseG = mkConj (pick slE es ++ [goalOf (exNode exE)])
          goal = case (mc, g) of
            (Nothing, _) -> Comp ";" [thenG, elseG]
            (Just _, Comp "if_commit" _) -> Comp "if_commit" [mkConj (pick slC cs), thenG, elseG]
            (Just _, _) -> ite (mkConj (pick slC cs)) thenG elseG
          info = Comp "branch" [g, sliceTerm slC, sliceTerm slT, sliceTerm slE]
          localScopes = cs ++ ts ++ es
          outerConsumed = [ x | x <- exConsumed exT ++ exConsumed exE, x `notElem` localScopes ]
      return (EX (enode "el_branch" vt k r goal [exNode exT, exNode exE] info)
                 (slNeeds slC `IS.union` slNeeds slE)
                 outerConsumed
                 (IS.unions [exConflicts exT, exConflicts exE, slConflicts slT, slConflicts slC, slConflicts slE]))
    -- A concatenation: plop2_chain/3 over one closure per part.
    chainOf mode parts = do
      cls <- mapM (closureFor mode) parts
      let goal = Comp "plop2_chain" [Int (fromIntegral k), mkList [ c | (c, _, _) <- cls ] (Atom "[]"), r]
          subs = [ Comp "cl" [Atom rule, p, c, info] | ((c, rule, info), p) <- zip cls parts ]
          needs = IS.unions [ clNeeds rule p c | ((c, rule, _), p) <- zip cls parts ]
          consumed = [ info | (_, "cl_spec", info) <- cls ]
                     ++ [ pg | (_, "cl_chain", Comp "chain" [pg, _]) <- cls ]
      return (EX (enode "el_chain" vt k r goal subs g) needs consumed IS.empty)
    clNeeds rule p c = case rule of
      "cl_static" -> IS.empty
      "cl_value" -> localVars env p
      "cl_chain" -> IS.unions [ localVars env x | Comp "plop2_value" [x] <- chainItems c ]
      _ -> IS.unions (map (localVars env) (goalArgs c))
    chainItems (Comp "plop2_chain_c" [l]) = maybe [] id (staticList l)
    chainItems _ = []
    -- call(Closure, J, R) gives element J of the part
    closureFor mode p = case staticElems mode p of
      Just xs -> return (Comp "plop2_static" [mkList xs (Atom "[]")], "cl_static", Atom "none")
      Nothing -> case p of
        Var w _ | not (IS.member w (envFull env))
                , Just (pg, pbefore, _) <- findProducer (cxBound cx) before w
                , Just (key, pos) <- partOutput pg w
                , okGround key pos pg pbefore -> do
            let usedAny = Set.unions [ M.findWithDefault Set.empty (Spec key pos jj) (envUsed env) | jj <- [1 .. k] ]
            mapM_ (\jj -> request (Spec key pos jj)) [1 .. k]
            requestDisp (key, pos, k)
            args' <- sequence [ if Set.member ix usedAny then return a else fresh "_"
                              | (ix, a) <- zip [0 ..] (goalArgs pg), ix /= pos ]
            return (Comp (dispName key pos k) args', "cl_spec", pg)
        Var w _ | not (IS.member w (envFull env))
                , Just (pg, pbefore, _) <- findProducer (cxBound cx) before w
                , Just (innerMode, innerParts) <- concatParts pg w -> do
            -- a part that is itself a concatenation: a nested chain
            inner <- mapM (closureForIn innerMode pbefore) innerParts
            let clo = Comp "plop2_chain_c" [mkList [ c | (c, _, _) <- inner ] (Atom "[]")]
                info = Comp "chain" [pg, mkList [ Comp "cl" [Atom rl, ip, c, inf] | ((c, rl, inf), ip) <- zip inner innerParts ] (Atom "[]")]
            return (clo, "cl_chain", info)
        _ -> return (Comp "plop2_value" [p], "cl_value", Atom "none")
    closureForIn mode bef p = producerExpr' mode bef p
    producerExpr' mode bef p =
      let cx' = cx { cxVisible = bef }
      in closureWith cx' mode p
    closureWith cx' mode p = case staticElems mode p of
      Just xs -> return (Comp "plop2_static" [mkList xs (Atom "[]")], "cl_static", Atom "none")
      Nothing -> do
        _ <- return cx'
        return (Comp "plop2_value" [p], "cl_value", Atom "none")
    concatParts pg w = case pg of
      Comp "append" [a, b, Var x _] | x == w -> Just (ListMode, [a, b])
      Comp f [a, b, Var x _] | x == w, f `elem` ["atom_concat", "string_concat"] -> Just (TextMode, [a, b])
      Comp "atomic_list_concat" [l, Var x _] | x == w, Just ps <- staticList l -> Just (TextMode, ps)
      Comp "atomic_list_concat" [l, sep, Var x _] | x == w, Just ps <- staticList l -> Just (TextMode, interleave sep ps)
      _ -> Nothing
    partOutput pg w = case goalKey pg of
      Just key | M.member key (progPreds (envProg env))
               , [pos] <- [ ix | (ix, Var x _) <- zip [0 ..] (goalArgs pg), x == w ]
               , not (IS.member w (IS.unions [ termVarIds a | (ix, a) <- zip [0 :: Int ..] (goalArgs pg), ix /= pos ])) ->
          Just (key, pos)
      _ -> Nothing
    okGround key pos pg pbefore =
      let gB = groundThrough (cxGround cx) pbefore
          usedAny = Set.unions [ M.findWithDefault Set.empty (Spec key pos jj) (envUsed env) | jj <- [1 .. k] ]
      in and [ IS.isSubsetOf (termVarIds a) gB | (ix, a) <- zip [0 ..] (goalArgs pg), ix /= pos, Set.member ix usedAny ]

data Mode = ListMode | TextMode

staticElems :: Mode -> Term -> Maybe [Term]
staticElems ListMode t = groundList t
  where
    groundList (Atom "[]") = Just []
    groundList (Comp "." [h, tl]) | IS.null (termVarIds h) = (h :) <$> groundList tl
    groundList _ = Nothing
staticElems TextMode t = case t of
  Atom a -> Just [ Atom [c] | c <- a ]
  Int x -> Just [ Atom [c] | c <- show x ]
  _ -> staticElems ListMode t

staticList :: Term -> Maybe [Term]
staticList (Atom "[]") = Just []
staticList (Comp "." [h, t]) = (h :) <$> staticList t
staticList _ = Nothing

interleave :: Term -> [Term] -> [Term]
interleave _ [] = []
interleave _ [x] = [x]
interleave s (x : xs) = x : s : interleave s xs

-- ---------------------------------------------------------------------------
-- Keeping, dropping (with a certificate) and consuming goals

data Slice = Slice
  { slKept :: [Int]
  , slDropped :: [(Int, Term)]
  , slConsumed :: [Int]
  , slNeeds :: IS.IntSet
  , slConflicts :: IS.IntSet
  }

sliceTerm :: Slice -> Term
sliceTerm sl = Comp "sl" [ mkList (map (Int . fromIntegral) (slKept sl)) (Atom "[]")
                         , mkList [ Comp "drop" [Int (fromIntegral i), c] | (i, c) <- slDropped sl ] (Atom "[]")
                         , mkList (map (Int . fromIntegral) (slConsumed sl)) (Atom "[]") ]

closeOver :: Env -> IS.IntSet -> IS.IntSet -> [Term] -> IS.IntSet -> [Term] -> Slice
closeOver env bound ground gs demand0 consumed =
  let annotated = zip3 [1 :: Int ..] (withProduced bound gs) (scanl groundAfter ground gs)
      step (ix, (g, prod), gnd) (sl, d)
        | g `elem` consumed =
            (sl { slConsumed = ix : slConsumed sl
                , slConflicts = slConflicts sl `IS.union` IS.intersection prod d }, d)
        | not (IS.null (IS.intersection prod d)) = (sl { slKept = ix : slKept sl }, d `IS.union` localVars env g)
        | Just cert <- totality (envProg env) gnd prod g = (sl { slDropped = (ix, cert) : slDropped sl }, d)
        | otherwise = (sl { slKept = ix : slKept sl }, d `IS.union` localVars env g)
      (sl0, dEnd) = foldr step (Slice [] [] [] IS.empty IS.empty, demand0) annotated
      prodAll = IS.unions [ p | (_, (_, p), _) <- annotated ]
  in sl0 { slNeeds = dEnd `IS.difference` prodAll }

-- | A certificate that a goal always succeeds exactly once and binds only
-- the variables it produces, given the variables ground before it.
totality :: Program -> IS.IntSet -> IS.IntSet -> Term -> Maybe Term
totality prog gnd prod g
  | maybe False (`M.member` progPreds prog) (goalKey g) = Nothing
  | otherwise = case g of
      Atom "true" -> cert "true"
      Atom "nl" -> cert "output"
      Comp f [_] | f `elem` ["write", "print", "writeln", "writeq", "write_canonical"] -> cert "output"
      Comp "=" [Var x _, t] | freshVar x t -> cert "fresh_unify"
      Comp "=" [t, Var x _] | freshVar x t -> cert "fresh_unify"
      Comp "is" [Var x _, e] | freshVar x e && gr e && arith e -> cert "arith"
      Comp f [a, Var x _]
        | f `elem` ["atom_codes", "atom_chars", "atom_length", "number_codes", "number_chars", "upcase_atom", "downcase_atom", "atomic_list_concat"]
        , gr a, freshVar x a -> cert "text"
      Comp "atomic_list_concat" [l, s, Var x _] | gr l && gr s && freshVar x (Comp "x" [l, s]) -> cert "text"
      Comp "char_code" [Var x _, code] | gr code && freshVar x code -> cert "text"
      Comp f [a, b, Var x _]
        | f `elem` ["atom_concat", "string_concat"], gr a, gr b, freshVar x (Comp "x" [a, b]) -> cert "text"
      Comp "append" [a, b, Var x _] | gr a && freshVar x (Comp "x" [a, b]) -> cert "append"
      Comp "length" [l, Var x _] | gr l && freshVar x l -> cert "length"
      Comp "reverse" [l, Var x _] | gr l && freshVar x l -> cert "reverse"
      _ -> Nothing
  where
    cert rule = Just (Comp "total" [Atom rule])
    gr t = IS.isSubsetOf (termVarIds t) gnd
    freshVar x t = IS.member x prod && not (IS.member x (termVarIds t))
    arith t = case t of
      Int _ -> True
      Var _ _ -> True
      Comp op [a, b] | op `elem` ["+", "-", "*"] -> arith a && arith b
      Comp "-" [a] -> arith a
      _ -> False

-- ---------------------------------------------------------------------------
-- Helpers written into every generated file (cut-free).

helperSource :: String
helperSource = unlines
  [ "% plop2_nth_r(+K, +T, -R): R = c(E) for element K of a list, or character K"
  , "% of an atom or integer; R = none if there is no such element."
  , "plop2_nth_r(K, T, R) :- ( plop2_nth_char(K, T, C) -> R = c(C) ; R = none )."
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
  , "% plop2_chain(+K, +Parts, -R): element K of the concatenation of the parts."
  , "% call(Part, J, RJ) gives element J of a part.  A part without element K has"
  , "% L < K elements, and element K of the whole is element K - L of the rest."
  , "plop2_chain(_, [], none)."
  , "plop2_chain(K, [P|Ps], R) :-"
  , "    call(P, K, R0),"
  , "    (   R0 = c(_)"
  , "    ->  R = R0"
  , "    ;   plop2_part_length(P, K, L), K1 is K - L, plop2_chain(K1, Ps, R)"
  , "    )."
  , "plop2_part_length(P, K, L) :-"
  , "    K1 is K - 1,"
  , "    (   K1 =:= 0"
  , "    ->  L = 0"
  , "    ;   call(P, K1, R1), ( R1 = c(_) -> L = K1 ; plop2_part_length(P, K1, L) )"
  , "    )."
  , "plop2_static(Es, J, R) :- plop2_nth_r(J, Es, R)."
  , "plop2_value(V, J, R) :- plop2_nth_r(J, V, R)."
  , "plop2_chain_c(Parts, J, R) :- plop2_chain(J, Parts, R)."
  ]
