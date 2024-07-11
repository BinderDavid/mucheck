{-# LANGUAGE RankNTypes #-}
module Test.MuCheck.Utils.SybSpec where

import Test.Hspec
import Control.Monad (MonadPlus, mplus, mzero)
import Test.MuCheck.MuOp (mkMpMuOp, MuOp)
import Data.Generics (GenericQ, mkQ, Data, Typeable, mkMp, listify, GenericM, gmapMo)
import Language.Haskell.Exts


-- | apply a mutating function on a piece of code one at a time
-- like somewhere (from so)
once :: MonadPlus m => GenericM m -> GenericM m
once f x = f x `mplus` gmapMo (once f) x

main :: IO ()
main = hspec spec

dummySrcLoc = SrcLoc "<unknown>.hs" 15 1

m1 a b = Match (dummySrcLoc)
           (Ident dummySrcLoc a)
           [PApp dummySrcLoc (UnQual dummySrcLoc (Ident dummySrcLoc b)) [],PLit dummySrcLoc (Signless dummySrcLoc) (Int dummySrcLoc 0 "0")]
           (UnGuardedRhs dummySrcLoc (Lit dummySrcLoc (Int dummySrcLoc 1 "1")))
           (Just (BDecls dummySrcLoc []))

replM :: MonadPlus m => Name SrcLoc -> m (Name SrcLoc)
replM (Ident l "x") = return $ Ident l "y"
replM t = mzero

spec :: Spec
spec = do
  describe "once" $ do
    it "apply a function once on exp" $ do
      (once (mkMp replM) (FunBind dummySrcLoc [m1 "y" "x"]) :: Maybe (Decl SrcLoc)) `shouldBe` Just (FunBind dummySrcLoc [m1 "y" "y"] :: (Decl SrcLoc))
    it "apply a function just once" $ do
      (once (mkMp replM) (FunBind dummySrcLoc [m1 "x" "x"]) :: Maybe (Decl SrcLoc)) `shouldBe` Just (FunBind dummySrcLoc [m1 "y" "x"] :: (Decl SrcLoc))
    it "apply a function just once if possible" $ do
      (once (mkMp replM) (FunBind dummySrcLoc [m1 "y" "y"]) :: Maybe (Decl SrcLoc)) `shouldBe` Nothing 
    it "should return all possibilities" $ do
      (once (mkMp replM) (FunBind dummySrcLoc [m1 "x" "x"]) :: [(Decl SrcLoc)]) `shouldBe`  ([FunBind dummySrcLoc [m1 "y" "x"], FunBind dummySrcLoc [m1 "x" "y"]] :: [(Decl SrcLoc)])
