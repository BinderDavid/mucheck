{-# LANGUAGE ImpredicativeTypes, Rank2Types, TupleSections, RecordWildCards #-}
-- | This module handles the mutation of different patterns.
module Test.MuCheck.Mutation where

import Language.Haskell.Exts(
  Literal(String),
  Exp(Lit),
  Match(Match),
  Pat(PVar),
  Module(Module),
  Name(Ident),
  Decl(FunBind, PatBind, AnnPragma),
  Annotation(Ann),
  Name(Symbol, Ident),
  prettyPrint,
  fromParseResult,
  parseModule,
  ModuleHead(..),
  ModuleName(..))
import Data.Generics (listify)
import Data.List(partition)
import Control.Monad (liftM)

import Test.MuCheck.Tix
import Test.MuCheck.MuOp
import Test.MuCheck.Utils.Common
import Test.MuCheck.Config
import Test.MuCheck.TestAdapter
import Test.MuCheck.Mutants

-- | The `genMutants` function is a wrapper to genMutantsWith with standard
-- configuraton
genMutants ::
     FilePath           -- ^ The module we are mutating
  -> FilePath           -- ^ Coverage information for the module
  -> IO (Int,[Mutant]) -- ^ Returns the covering mutants produced, and original length.
genMutants = genMutantsWith defaultConfig

-- | The `genMutantsWith` function takes configuration function to mutate,
-- function to mutate, filename the function is defined in, and produces
-- mutants in the same directory as the filename, and returns the number
-- of mutants produced.
genMutantsWith ::
     Config                     -- ^ The configuration to be used
  -> FilePath                   -- ^ The module we are mutating
  -> FilePath                   -- ^ Coverage information for the module
  -> IO (Int, [Mutant])         -- ^ Returns the covered mutants produced, and the original number
genMutantsWith _config filename  tix = do
      f <- readFile filename

      let modul = getModuleName (getASTFromStr f)
          mutants :: [Mutant]
          mutants = genMutantsForSrc defaultConfig f

      -- We have a choice here. We could allow users to specify test specific
      -- coverage rather than a single coverage. This can further reduce the
      -- mutants.
      c <- getUnCoveredPatches tix modul
      -- check if the mutants span is within any of the covered spans.
      return $ case c of
                            Nothing -> (-1, mutants)
                            Just v -> (length mutants, removeUncovered v mutants)

-- | Remove mutants that are not covered by any tests
removeUncovered :: [Span] -> [Mutant] -> [Mutant]
removeUncovered uspans mutants = filter isMCovered mutants -- get only covering mutants.
  where  isMCovered :: Mutant -> Bool
         -- | is it contained in any of the spans? if it is, then return false.
         isMCovered Mutant{..} = not $ any (insideSpan _mspan) uspans

-- | Get the module name from ast
getModuleName :: Module t -> String
getModuleName (Module _ (Just (ModuleHead _ (ModuleName _ name) _ _ )) _ _ _) = name
getModuleName _ = ""

-- | The `genMutantsForSrc` takes the function name to mutate, source where it
-- is defined, and returns the mutated sources
genMutantsForSrc ::
     Config                   -- ^ Configuration
  -> String                   -- ^ The module we are mutating
  -> [Mutant] -- ^ Returns the mutants
genMutantsForSrc config src = map (toMutant . apTh (prettyPrint . withAnn)) $ programMutants config ast
  where origAst = getASTFromStr src
        (onlyAnn, noAnn) = splitAnnotations origAst
        ast = putDecl origAst noAnn
        withAnn mast = putDecl mast $ getDecl mast ++ onlyAnn



-- | Split declarations of the module to annotated and non annotated.
splitAnnotations :: Module_ -> ([Decl_], [Decl_])
splitAnnotations ast = partition fn $ getDecl ast
  where fn x = (functionName x ++ pragmaName x) `elem` getAnnotatedTests ast
        -- only one of pragmaName or functionName will be present at a time.

-- | Returns the annotated tests and their annotations
getAnnotatedTests :: Module_ -> [String]
getAnnotatedTests ast = concatMap (getAnn ast) ["Test","TestSupport"]

-- | Get the embedded declarations from a module.
getDecl :: Module_ -> [Decl_]
getDecl (Module _ _ _ _ decls) = decls
getDecl _ = []

-- | Put the given declarations into the given module
putDecl :: Module_ -> [Decl_] -> Module_
putDecl (Module a b c d _) decls = Module a b c d decls
putDecl m _ = m


-- AST/module-related operations

-- | Returns the AST from the file
getASTFromStr :: String -> Module_
getASTFromStr fname = fromParseResult $ parseModule fname

-- | get all annotated functions
getAnn :: Module_ -> String -> [String]
getAnn m s =  [conv name | Ann _l name _exp <- listify isAnn m]
  where isAnn :: Annotation_ -> Bool
        isAnn (Ann _l (Symbol _lsy _name) (Lit _ll (String _ls e _))) = e == s
        isAnn (Ann _l (Ident _lid _name) (Lit _ll (String _ls e _))) = e == s
        isAnn _ = False
        conv (Symbol _l n) = n
        conv (Ident _l n) = n

-- | given the module name, return all marked tests
getAllTests :: String -> IO [String]
getAllTests modname = liftM allTests $ readFile modname

-- | Given module source, return all marked tests
allTests :: String -> [String]
allTests modsrc = getAnn (getASTFromStr modsrc) "Test"

-- | The name of a function
functionName :: Decl_ -> String
functionName (FunBind _l (Match _ (Ident _li n) _ _ _ : _)) = n
functionName (FunBind _l (Match _ (Symbol _ls n) _ _ _ : _)) = n
-- we also consider where clauses
functionName (PatBind _ (PVar _lpv (Ident _li n)) _ _)          = n
functionName _                                   = []

-- | The identifier of declared pragma
pragmaName :: Decl_ -> String
pragmaName (AnnPragma _ (Ann _l (Ident _li n) (Lit _ll (String _ls _t _)))) = n
pragmaName _ = []

-- but not let, because it has a different type, and for our purposes
-- this is sufficient.
-- (Let Binds Exp) :: Exp

