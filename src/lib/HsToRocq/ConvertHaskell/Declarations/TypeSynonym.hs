{-# LANGUAGE FlexibleContexts, OverloadedStrings, PatternSynonyms, MultiParamTypeClasses #-}

module HsToRocq.ConvertHaskell.Declarations.TypeSynonym (SynBody(..), convertSynDecl) where

import Prelude hiding (Num)

import Control.Lens

import GHC hiding (Name)
import qualified GHC

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S

import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util (pattern Var, appList, binderIdents, mkTypedBinder)
import HsToRocq.Rocq.FreeVars
import HsToRocq.Util.FVs

import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.HsType
import HsToRocq.Edits.Types

--------------------------------------------------------------------------------

data SynBody = SynBody Qualid [Binder] (Maybe Term) Term
             deriving (Eq, Ord, Read, Show)

instance HasBV Qualid SynBody where
  bvOf (SynBody name args oty def) =
    binder name <> bindsNothing (foldScopes bvOf args $ fvOf oty <> fvOf def)

-- might make sense to use ConversionMonad instead
convertSynDecl :: LocalConvMonad r m
               => GenLocated l GHC.Name -> [LHsTyVarBndr flag GhcRn] -> LHsType GhcRn
               -> m SynBody
convertSynDecl name args def  = do
  coqName <- freeVar $ unLoc name
  rawParams <- convertLHsTyVarBndrs Coq.Explicit args
  q <- var TypeNS (unLoc name)
  kinds <- view (edits.dataKinds.at q)
  let annotate (ExplicitBinder n) (Just k) = mkTypedBinder Explicit n k
      annotate binder _ = binder
      params = zipWith annotate rawParams (maybe [] (map Just . NE.toList) kinds ++ repeat Nothing)
  rhs    <- convertLHsType def
  let (params', rhs') = etaContract params rhs
  SynBody q params'
          <$> view (edits.typeSynonymTypes . at coqName . to (fmap Var))
          <*> pure (rhs' `InScope` "type")

-- Eta-contracting type synonyms allows Coq’s instance resolution mechanism
-- to look though type synonym more easily.
etaContract :: [Binder] -> Term -> ([Binder], Term)
etaContract bndrs (App f args)
    = let (rbinders, rargs) = go (reverse bndrs) (reverse (NE.toList args))
      in (reverse rbinders, appList f (reverse rargs))
  where
    go (b:bs) (a:as)
        | PosArg (Qualid v) <- a
        , [v'] <- toListOf binderIdents b
        , v == v'
        , v' `S.notMember` getFreeVars f
        , v' `S.notMember` getFreeVars as
        = go bs as
    go bs as = (bs, as)
etaContract b t = (b,t)
