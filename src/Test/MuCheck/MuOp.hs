{-#  LANGUAGE Rank2Types, FlexibleInstances, ConstraintKinds #-}
-- | Mutation operators
module Test.MuCheck.MuOp (MuOp
          , Mutable(..)
          , (==>*)
          , (*==>*)
          , (~~>)
          , mkMpMuOp
          , same
          , Module_
          , Name_
          , QName_
          , QOp_
          , Exp_
          , Decl_
          , Literal_
          , GuardedRhs_
          , Annotation_
          , getSpan
          ) where

import qualified Data.Generics as G
import Control.Monad (MonadPlus, mzero)

import Language.Haskell.Exts(Module, Name, QName, QOp, Exp, Decl, Literal, GuardedRhs, Annotation, SrcSpanInfo(..), srcSpanStart, srcSpanEnd, prettyPrint, Pretty(), Annotated(..))

-- | SrcSpanInfo wrapper
type Module_ = Module SrcSpanInfo
-- | SrcSpanInfo wrapper
type Name_ = Name SrcSpanInfo
-- | SrcSpanInfo wrapper
type QName_ = QName SrcSpanInfo
-- | SrcSpanInfo wrapper
type QOp_ = QOp SrcSpanInfo
-- | SrcSpanInfo wrapper
type Exp_ = Exp SrcSpanInfo
-- | SrcSpanInfo wrapper
type Decl_ = Decl SrcSpanInfo
-- | SrcSpanInfo wrapper
type Literal_ = Literal SrcSpanInfo
-- | SrcSpanInfo wrapper
type GuardedRhs_ = GuardedRhs SrcSpanInfo
-- | SrcSpanInfo wrapper
type Annotation_ = Annotation SrcSpanInfo


-- | MuOp constructor used to specify mutation transformation
data MuOp = N  (Name_, Name_)
          | QN (QName_, QName_)
          | QO (QOp_, QOp_)
          | E  (Exp_, Exp_)
          | D  (Decl_, Decl_)
          | L  (Literal_, Literal_)
          | G  (GuardedRhs_, GuardedRhs_)
  deriving Eq


-- How do I get the Annotated (a SrcSpanInfo) on apply's signature?
-- | getSpan retrieve the span as a tuple
getSpan :: MuOp -> (Int, Int, Int, Int)
getSpan m = (startLine, startCol, endLine, endCol)
  where (endLine, endCol) = srcSpanEnd lspan
        (startLine, startCol) = srcSpanStart lspan
        getSpan' (N  (a,_)) = ann a
        getSpan' (QN (a,_)) = ann a
        getSpan' (QO (a,_)) = ann a
        getSpan' (E  (a,_)) = ann a
        getSpan' (D  (a,_)) = ann a
        getSpan' (L  (a,_)) = ann a
        getSpan' (G  (a,_)) = ann a
        lspan = srcInfoSpan $ getSpan' m

-- | The function `same` applies on a `MuOP` determining if transformation is
-- between same values.
same :: MuOp -> Bool
same (N (x,y)) = x == y
same (QN (x,y)) = x == y
same (QO (x,y)) = x == y
same (E (x,y)) = x == y
same (D (x,y)) = x == y
same (L (x,y)) = x == y
same (G (x,y)) = x == y

-- | A wrapper over mkMp
mkMpMuOp :: (MonadPlus m, G.Typeable a) => MuOp -> a -> m a
mkMpMuOp (N (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (QN (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (QO (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (E (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (D (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (L (x,y)) = G.mkMp (x ~~> y) 
mkMpMuOp (G (x,y)) = G.mkMp (x ~~> y) 

-- | Show a specified mutation
showM :: (Show a1, Show a, Pretty a, Pretty a1) => (a, a1) -> String
showM (s, t) = "{\n" ++ prettyPrint s ++ "\n} ==> {\n" ++ prettyPrint t ++ "\n}"

-- | MuOp instance for Show
instance Show MuOp where
  show  (N p) =  showM p
  show (QN p) = showM p
  show (QO p) = showM p
  show (E p) = showM p
  show (D p) = showM p
  show (L p) = showM p
  show (G p) = showM p

-- | Mutation operation representing translation from one fn to another fn.
class Mutable a where
  (==>) :: a -> a -> MuOp

-- | The function `==>*` pairs up the given element with all elements of the
-- second list, and applies `==>` on them.
(==>*) :: Mutable a => a -> [a] -> [MuOp]
(==>*) x = map (x ==>)

-- | The function `*==>*` pairs up all elements of first list with all elements
-- of second list and applies `==>` between them.
(*==>*) :: Mutable a => [a] -> [a] -> [MuOp]
xs *==>* ys = concatMap (==>* ys) xs

-- | The function `~~>` accepts two values, and returns a function
-- that if given a value equal to first, returns second
-- we handle x ~~> x separately
(~~>) :: (MonadPlus m, Eq a) => a -> a -> a -> m a
x ~~> y = \z -> if z == x then return y else mzero

-- | Name instance for Mutable
instance Mutable Name_ where
  (==>) = (N .) . (,)

-- | QName instance for Mutable
instance Mutable QName_ where
  (==>) = (QN .) . (,)

-- | QOp instance for Mutable
instance Mutable QOp_ where
  (==>) = (QO .) . (,)

-- | Exp instance for Mutable
instance Mutable Exp_ where
  (==>) = (E .) . (,)

-- | Exp instance for Mutable
instance Mutable Decl_ where
  (==>) = (D .) . (,)

-- | Literal instance for Mutable
instance Mutable Literal_ where
  (==>) = (L .) . (,)

-- | GuardedRhs instance for Mutable
instance Mutable GuardedRhs_ where
  (==>) = (G .) . (,)

