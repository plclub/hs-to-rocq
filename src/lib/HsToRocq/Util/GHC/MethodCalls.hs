{-# LANGUAGE CPP, ScopedTypeVariables #-}
module HsToRocq.Util.GHC.MethodCalls (MethodCalls, MethodSites, methodCalls) where

import qualified GHC
import qualified Data.Map.Strict as M
import qualified Data.Set as S

#if __GLASGOW_HASKELL__ >= 910
import Data.Data (Data)
import Data.Generics (everythingBut, extQ, mkQ)
import GHC.Core (Expr(Var))
import GHC.Data.Bag (bagToList)
import GHC.Tc.Types.Evidence (EvBind(..), EvTerm(..), HsWrapper(..), TcEvBinds(..))
import GHC.Types.Id (Id, isClassOpId_maybe, isDFunId)
import GHC.Types.Name (nameStableString)
import Data.Maybe (isJust)
#endif

type MethodSites = S.Set (GHC.Name, GHC.RealSrcSpan)
type MethodCalls = M.Map String MethodSites

#if __GLASGOW_HASKELL__ >= 910

-- A monomorphic instance has a single, unapplied dictionary. Follow only
-- exact variable aliases to its dfun. A given dictionary, or a dictionary
-- for a component type, must not turn into a recursive call.
methodCalls :: GHC.TypecheckedModule -> MethodCalls
methodCalls tm = M.fromListWith S.union
  [(nameStableString (GHC.getName df), S.singleton (GHC.getName op, s))
  | (s, op, ev) <- collect applications src
  , Just df <- [resolve S.empty ev]]
 where
  src = GHC.tm_typechecked_source tm
  aliases = M.fromList (collect aliasGroup src)
  aliasGroup (EvBinds bs) = concatMap alias (bagToList bs)
  aliasGroup (TcEvBinds _) = []
  alias (EvBind lhs (EvExpr (Var rhs)) _) = [(GHC.getName lhs,rhs)]
  alias _ = []
  resolve seen v
    | isDFunId v = Just v
    | n `S.member` seen = Nothing
    | otherwise = M.lookup n aliases >>= resolve (S.insert n seen)
    where n = GHC.getName v
  applications :: GHC.LHsExpr GHC.GhcTc -> [(GHC.RealSrcSpan, Id, Id)]
  applications e | GHC.RealSrcSpan s _ <- GHC.getLocA e
                 , GHC.XExpr (GHC.WrapExpr (GHC.HsWrap w (GHC.HsVar _ (GHC.L _ op)))) <- GHC.unLoc e
                 , isJust (isClassOpId_maybe op)
                 , [ev] <- evidence w = [(s,op,ev)]
  applications _ = []
  evidence (WpEvApp (EvExpr (Var v))) = [v]
  evidence (WpCompose u v) = evidence u ++ evidence v
  evidence _ = []

-- GHC metadata can be cyclic; visit source expressions and evidence
-- bindings, not the types or IdInfo stored in them.
collect :: (Data a, Data b) => (a -> [c]) -> b -> [c]
collect f = everythingBut (++)
  ((((([],False) `mkQ` (\x -> (f x, False)))
     `extQ` (\(_ :: GHC.Type) -> stop))
     `extQ` (\(_ :: Id) -> stop))
     `extQ` (\(_ :: GHC.Name) -> stop))
 where stop = ([],True)
#else
methodCalls :: GHC.TypecheckedModule -> MethodCalls
methodCalls _ = M.empty
#endif
