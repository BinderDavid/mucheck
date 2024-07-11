{-# LANGUAGE  TupleSections, RankNTypes #-}
module Test.MuCheck.Mutants (programMutants, selectLitOps, selectBLitOps, selectIfElseBoolNegOps, selectGuardedBoolNegOps, selectFnMatches) where

import Language.Haskell.Exts(
    Literal(Int, Char, Frac, String, PrimInt, PrimChar, PrimFloat, PrimDouble, PrimWord, PrimString),
    Exp(App, Var, If),
    QName(UnQual),
    Stmt(Qualifier),
    Name(Ident),
    Decl(FunBind),
    GuardedRhs(GuardedRhs),
    Name(Symbol, Ident),
    SrcSpanInfo(..),
    SrcSpan(..))

import Data.List(nub, (\\), permutations, subsequences)


import Test.MuCheck.MuOp
    ( (==>*),
      getSpan,
      mkMpMuOp,
      same,
      Decl_,
      Exp_,
      GuardedRhs_,
      Literal_,
      Module_,
      MuOp,
      Mutable,
      Name_ )
import Test.MuCheck.Config
    ( Config(muOp),
      FnOp(_type, _fns),
      FnType(FnSymbol, FnIdent),
      MuVar(..) )

import Data.Generics (Data, GenericM, gmapMo, Typeable, mkMp, listify)
import Control.Monad (MonadPlus, mplus)
import Data.Maybe(isJust)

type Span = (Int, Int, Int, Int)
-- | apply a mutating function on a piece of code one at a time
-- like somewhere (from so)
once :: MonadPlus m => GenericM m -> GenericM m
once f x = f x `mplus` gmapMo (once f) x

-- | The function `relevantOps` does two filters. For the first, it
-- removes spurious transformations like "Int 1 ~~> Int 1". Secondly, it
-- tries to apply the transformation to the given program on some element
-- if it does not succeed, then we discard that transformation.
relevantOps :: (Data a, Eq a) => a -> [(MuVar, MuOp)] -> [(MuVar, MuOp)]
relevantOps m oplst = filter (relevantOp m) $ filter (not . same . snd) oplst
  -- check if an operator can be applied to a program
  where relevantOp m' (_v, op) = isJust $ once (mkMpMuOp op) m'

-- | convert a tuple with element and second array to an array of
-- tuples by repeating the first element 
spread :: (a, [b]) -> [(a, b)]
spread (a,lst) = map (a,) lst

-- | The `choose` function generates subsets of a given size
choose :: [a] -> Int -> [[a]]
choose xs n = filter (\x -> length x == n) $ subsequences xs

-- | Produce all mutants after applying all operators
programMutants ::
     Config                   -- ^ Configuration
  -> Module_                  -- ^ Module to mutate
  -> [(MuVar, Span, Module_)] -- ^ Returns mutated modules
programMutants config ast =  nub $ mutatesN (applicableOps config ast) ast fstOrder
  where fstOrder = 1 -- first order

-- | First and higher order mutation. The actual apply of mutation operators,
-- and generation of mutants happens here.
-- The third argument specifies whether it's first order or higher order
mutatesN ::
     [(MuVar,MuOp)]     -- ^ Applicable Operators
  -> Module_            -- ^ Module to mutate
  -> Int                -- ^ Order of mutation (usually 1 - first order)
  -> [(MuVar, Span, Module_)] -- ^ Returns the mutated module
mutatesN os ast = mutatesN' os (MutateOther [], (0,0,0,0), ast)
  where mutatesN' ops ms 1 = concat [mutate op ms | op <- ops ]
        mutatesN' ops ms c = concat [mutatesN' ops m 1 | m <- mutatesN' ops ms $ pred c]

-- | Given a function, generate all mutants after applying applying
-- op once (op might be applied at different places).
-- E.g.: if the operator is (op = "<" ==> ">") and there are two instances of
-- "<" in the AST, then it will return two AST with each replaced.
mutate :: (MuVar, MuOp) -> (MuVar, Span, Module_) -> [(MuVar, Span, Module_)]
mutate (v, op) (_v, _s, m) = map (v, getSpan op, ) $ once (mkMpMuOp op) m \\ [m]


-- | Returns all mutation operators
applicableOps ::
     Config                   -- ^ Configuration
  -> Module_                  -- ^ Module to mutate
  -> [(MuVar,MuOp)]           -- ^ Returns mutation operators
applicableOps config ast = relevantOps ast opsList
  where opsList = concatMap spread [
            (MutatePatternMatch, selectFnMatches ast),
            (MutateValues, selectLiteralOps ast),
            (MutateFunctions, selectFunctionOps (muOp config) ast),
            (MutateNegateIfElse, selectIfElseBoolNegOps ast),
            (MutateNegateGuards, selectGuardedBoolNegOps ast)]


-- | For valops, we specify how any given literal value might
-- change. So we take a predicate specifying how to recognize the literal
-- value, a list of mappings specifying how the literal can change, and the
-- AST, and recurse over the AST looking for literals that match our predicate.
-- When we find any, we apply the given list of mappings to them, and produce
-- a MuOp mapping between the original value and transformed value. This list
-- of MuOp mappings are then returned.
selectValOps :: (Typeable b, Mutable b) => (b -> Bool) -> (b -> [b]) -> Module_ -> [MuOp]
selectValOps predicate f m = concat [ x ==>* f x |  x <- vals ]
  where vals = listify predicate m

-- | Look for literal values in AST, and return applicable MuOp transforms.
selectLiteralOps :: Module_ -> [MuOp]
selectLiteralOps m = selectLitOps m ++ selectBLitOps m

-- | Look for literal values in AST, and return applicable MuOp transforms.
-- Unfortunately booleans are not handled here.
selectLitOps :: Module_ -> [MuOp]
selectLitOps = selectValOps isLit convert
  where isLit :: Literal_ -> Bool
        isLit Int{} = True
        isLit PrimInt{} = True
        isLit Char{} = True
        isLit PrimChar{} = True
        isLit Frac{} = True
        isLit PrimFloat{} = True
        isLit PrimDouble{} = True
        isLit String{} = True
        isLit PrimString{} = True
        isLit PrimWord{} = True
        convert (Int l i _) = map (apX (Int l)) $ nub [i + 1, i - 1, 0, 1]
        convert (PrimInt l i _) = map (apX (PrimInt l)) $ nub [i + 1, i - 1, 0, 1]
        convert (Char l c _) = map (apX (Char l)) [pred c, succ c]
        convert (PrimChar l c _) = map (apX (Char l)) [pred c, succ c]
        convert (Frac l f _) = map (apX (Frac l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.1]
        convert (PrimFloat l f _) = map (apX (PrimFloat l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.0]
        convert (PrimDouble l f _) = map (apX (PrimDouble l)) $ nub [f + 1.0, f - 1.0, 0.0, 1.0]
        convert (String l _ _) = map (apX (String l)) $ nub [""]
        convert (PrimString l _ _) = map (apX (PrimString l)) $ nub [""]
        convert (PrimWord l i _) = map (apX (PrimWord l)) $ nub [i + 1, i - 1, 0, 1]
        apX :: (t1 -> [a] -> t) -> t1 -> t
        apX fn i = fn i []

-- | Convert Boolean Literals
--
-- > (True, False)
--
-- becomes
--
-- > (False, True)

selectBLitOps :: Module_ -> [MuOp]
selectBLitOps = selectValOps isLit convert
  where isLit :: Name_ -> Bool
        isLit (Ident _l "True") = True
        isLit (Ident _l "False") = True
        isLit _ = False
        convert (Ident l "True") = [Ident l "False"]
        convert (Ident l "False") = [Ident l "True"]
        convert _ = []

-- | Negating boolean in if/else statements
--
-- > if True then 1 else 0
--
-- becomes
--
-- > if True then 0 else 1

selectIfElseBoolNegOps :: Module_ -> [MuOp]
selectIfElseBoolNegOps = selectValOps isIf convert
  where isIf :: Exp_ -> Bool
        isIf If{} = True
        isIf _    = False
        convert (If l e1 e2 e3) = [If l e1 e3 e2]
        convert _ = []

-- | Negating boolean in Guards
-- | negate guarded booleans in guarded definitions
--
-- > myFn x | x == 1 = True
-- > myFn   | otherwise = False
--
-- becomes
--
-- > myFn x | not (x == 1) = True
-- > myFn   | otherwise = False
selectGuardedBoolNegOps :: Module_ -> [MuOp]
selectGuardedBoolNegOps = selectValOps isGuardedRhs convert
  where isGuardedRhs :: GuardedRhs_ -> Bool
        isGuardedRhs GuardedRhs{} = True
        convert (GuardedRhs l stmts expr) = [GuardedRhs l s expr | s <- once (mkMp boolNegate) stmts]
        boolNegate _e@(Qualifier _l (Var _lv (UnQual _lu (Ident _li "otherwise")))) = [] -- VERIFY
        boolNegate (Qualifier l expr) = [Qualifier l (App l_ (Var l_ (UnQual l_ (Ident l_ "not"))) expr)]
        boolNegate _x = [] -- VERIFY

-- | dummy 
l_ :: SrcSpanInfo
l_ = SrcSpanInfo (SrcSpan "" 0 0 0 0) []


-- | Generate all operators for permuting and removal of pattern guards from
-- function definitions
--
-- > myFn (x:xs) = False
-- > myFn _ = True
--
-- becomes
--
-- > myFn _ = True
-- > myFn (x:xs) = False
--
-- > myFn _ = True
--
-- > myFn (x:xs) = False

selectFnMatches :: Module_ -> [MuOp]
selectFnMatches = selectValOps isFunct convert
  where isFunct :: Decl_ -> Bool
        isFunct FunBind{} = True
        isFunct _    = False
        convert (FunBind l ms) = map (FunBind l) $ filter (/= ms) (permutations ms ++ removeOneElem ms)
        convert _ = []

-- | Generate all operators for permuting symbols like binary operators
-- Since we are looking for symbols, we are reasonably sure that it is not
-- locally bound to a variable.
selectSymbolFnOps :: Module_ -> [String] -> [MuOp]
selectSymbolFnOps m s = selectValOps isBin convert m
  where isBin :: Name_ -> Bool
        isBin (Symbol _l n) | n `elem` s = True
        isBin _ = False
        convert (Symbol l n) = map (Symbol l) $ filter (/= n) s
        convert _ = []

-- | Generate all operators for permuting commonly used functions (with
-- identifiers).
selectIdentFnOps :: Module_ -> [String] ->  [MuOp]
selectIdentFnOps m s = selectValOps isCommonFn convert m
  where isCommonFn :: Exp_ -> Bool
        isCommonFn (Var _lv (UnQual _lu (Ident _l n))) | n `elem` s = True
        isCommonFn _ = False
        convert (Var lv_ (UnQual lu_ (Ident li_ n))) = map  (Var lv_ . UnQual lu_ . Ident li_) $ filter (/= n) s
        convert _ = []

-- | Generate all operators depending on whether it is a symbol or not.
selectFunctionOps :: [FnOp] -> Module_ -> [MuOp]
selectFunctionOps fo f = concatMap (selectIdentFnOps f) idents ++ concatMap (selectSymbolFnOps f) syms
  where idents = map _fns $ filter (\a -> _type a == FnIdent) fo
        syms = map _fns $ filter (\a -> _type a == FnSymbol) fo

-- (Var l (UnQual l (Ident l "ab")))
-- (App l (Var l (UnQual l (Ident l "head"))) (Var l (UnQual l (Ident l "b"))))
-- (App l (App l (Var l (UnQual l (Ident l "head"))) (Var l (UnQual l (Ident l "a")))) (Var l (UnQual l (Ident l "b")))))
-- (InfixApp l (Var l (UnQual l (Ident l "a"))) (QVarOp l (UnQual l (Symbol l ">"))) (Var l (UnQual l (Ident l "b"))))
-- (InfixApp l (Var l (UnQual l (Ident l "a"))) (QVarOp l (UnQual l (Ident l "x"))) (Var l (UnQual l (Ident l "b"))))

-- | Generate sub-arrays with one less element except when we have only
-- a single element.
removeOneElem :: Eq t => [t] -> [[t]]
removeOneElem [_] = []
removeOneElem l = choose l (length l - 1)
