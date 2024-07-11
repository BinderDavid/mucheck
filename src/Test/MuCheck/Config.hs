{-# LANGUAGE MultiWayIf #-}
-- | Configuration module
module Test.MuCheck.Config where


-- | For function mutations, whether the function is a symbol or an identifier
-- for example,`head` is an identifier while `==` is a symbol.
data FnType = FnSymbol | FnIdent
  deriving (Eq, Show)

-- | User defined function groups. Indicate whether the functions are symbols
-- or identifiers, and also the group of functions to interchange for.
-- We dont allow mixing of identifiers and functions for now (harder to
-- match)
data FnOp = FnOp {_type :: FnType, _fns :: [String]}
  deriving (Eq, Show)


-- | predicates ["pred", "id", "succ"]
predNums :: [String]
predNums = ["pred", "id", "succ"]

-- | functions on lists ["sum", "product", "maximum", "minimum", "head", "last"]
arithLists :: [String]
arithLists = ["sum", "product", "maximum", "minimum", "head", "last"]


-- | comparison operators ["<", ">", "<=", ">=", "/=", "=="]
comparators :: [String]
comparators = ["<", ">", "<=", ">=", "/=", "=="]

-- | binary arithmetic ["+", "-", "*", "/"]
binAriths :: [String]
binAriths = ["+", "-", "*", "/"]

-- | The configuration options
-- if 1 is provided, all mutants are selected for that kind, and 0 ensures that
-- no mutants are picked for that kind. Any fraction in between causes that
-- many mutants to be picked randomly from the available pool
data Config = Config {
-- | Mutation operators on operator or function replacement
  muOp :: [FnOp]
-- | Mutate pattern matches for functions?
-- for example
--
-- > first [] = Nothing
-- > first (x:_) = Just x
--
-- is mutated to
--
-- > first (x:_) = Just x
-- > first [] = Nothing
  , doMutatePatternMatches :: Rational
-- | Mutates integer values by +1 or -1 or by replacing it with 0 or 1
  , doMutateValues :: Rational
-- | Mutates operators and functions, that is
--
-- > i + 1
--
-- becomes
--
-- > i - 1
--
-- > i * 1
--
-- > i / 1
  , doMutateFunctions :: Rational
-- | negate if conditions, that is
--
-- > if True then 1 else 0
--
-- becomes
--
-- > if True then 0 else 1
  , doNegateIfElse :: Rational
-- | negate guarded booleans in guarded definitions
--
-- > myFn x | x == 1 = True
-- > myFn   | otherwise = False
--
-- becomes
--
-- > myFn x | not (x == 1) = True
-- > myFn   | otherwise = False
  , doNegateGuards :: Rational
-- | Maximum number of mutants to generate.
  , maxNumMutants :: Int
-- | Generation mode, can be traditional (firstOrder) and
-- higher order (higher order is experimental)
  }
  deriving Show

-- | The default configuration
defaultConfig :: Config
defaultConfig = Config {
    muOp = [
      FnOp {_type=FnIdent, _fns= predNums},FnOp {_type=FnIdent, _fns= arithLists},
      FnOp {_type=FnSymbol, _fns= comparators},FnOp {_type=FnSymbol, _fns=binAriths}]
  , doMutatePatternMatches = 1.0
  , doMutateValues = 1.0
  , doMutateFunctions = 1.0
  , doNegateIfElse = 1.0
  , doNegateGuards = 1.0
  , maxNumMutants = 300
  }

-- | Enumeration of different variants of mutations
data MuVar = MutatePatternMatch
           | MutateValues
           | MutateFunctions
           | MutateNegateIfElse
           | MutateNegateGuards
           | MutateOther String
  deriving (Eq, Show)

-- | getSample returns the fraction in config corresponding to the enum passed
-- in
getSample :: MuVar -> Config -> Rational
getSample MutatePatternMatch c = doMutatePatternMatches c
getSample MutateValues       c = doMutateValues c
getSample MutateFunctions    c = doMutateFunctions c
getSample MutateNegateIfElse c = doNegateIfElse c
getSample MutateNegateGuards c = doNegateGuards c
getSample MutateOther{} _c = 1

-- | similarity between two mutation variants. For ease of use, MutateOther is
-- treated differently. For MutateOther, if the string is empty, then it is
-- matched against any other MutateOther.
similar :: MuVar -> MuVar -> Bool
similar (MutateOther a) (MutateOther b) = if | null a  -> True
                                             | null b -> True
                                             | otherwise -> a == b
similar x y = x == y

