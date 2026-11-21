{-# LANGUAGE CPP, ScopedTypeVariables #-}
module HsToRocq.Util.GHC.Callbacks (CallbackUses, callbackUses) where

import qualified GHC
import qualified Data.Map as M

#if __GLASGOW_HASKELL__ >= 910
import Data.Data (Data)
import Data.Generics (everythingBut, extQ, mkQ)
import qualified Data.Set as S
import GHC.Core.Type (splitForAllTyVars)
import GHC.Tc.Types.Evidence (HsWrapper(..))
import GHC.Types.Var (Var, varType)

-- Only lambda-bound polymorphic parameters need this information. The
-- renamed tree has the source structure but no specialization evidence.
type CallbackUses = M.Map (GHC.Name, GHC.RealSrcSpan) [GHC.Type]

callbackUses :: GHC.TypecheckedModule -> CallbackUses
callbackUses = walk callback . GHC.tm_typechecked_source
 where
  callback :: GHC.Match GHC.GhcTc (GHC.LHsExpr GHC.GhcTc) -> CallbackUses
  callback m | GHC.LamAlt{} <- GHC.m_ctxt m
             , let names = S.fromList
                     [GHC.getName v | p <- GHC.m_pats m
                      , GHC.VarPat _ (GHC.L _ v) <- [GHC.unLoc p]
                      , not (null (fst (splitForAllTyVars (varType v))))]
             , not (S.null names) = walk (occurrence names) (GHC.m_grhss m)
  callback _ = M.empty

  occurrence :: S.Set GHC.Name -> GHC.LHsExpr GHC.GhcTc -> CallbackUses
  occurrence names e
    | GHC.RealSrcSpan s _ <- GHC.getLocA e
    , Just (v, args) <- application (GHC.unLoc e)
    , S.member (GHC.getName v) names = M.singleton (GHC.getName v, s) args
    | otherwise = M.empty

  application :: GHC.HsExpr GHC.GhcTc -> Maybe (Var, [GHC.Type])
  application (GHC.HsVar _ (GHC.L _ v)) = Just (v, [])
  application (GHC.HsAppType t f _) = append [t] (GHC.unLoc f)
  application (GHC.XExpr (GHC.WrapExpr (GHC.HsWrap w e))) =
    types w >>= (`append` e)
  application _ = Nothing
  append ts e = do (v, us) <- application e; pure (v, us ++ ts)
  types WpHole = Just []
  types (WpTyApp t) = Just [t]
  types (WpCompose u v) = (++) <$> types v <*> types u
  types _ = Nothing

-- Stop at compiler metadata; only descend into source syntax.
walk :: (Data a, Data b) => (a -> CallbackUses) -> b -> CallbackUses
walk f = everythingBut M.union
  (((((M.empty, False) `mkQ` (\x -> (f x, False)))
      `extQ` (\(_ :: GHC.Type) -> stop))
      `extQ` (\(_ :: Var) -> stop))
      `extQ` (\(_ :: GHC.Name) -> stop))
 where stop = (M.empty, True)
#else
type CallbackUses = M.Map () ()
callbackUses :: GHC.TypecheckedModule -> CallbackUses
callbackUses _ = M.empty
#endif
