{-# LANGUAGE CPP, LambdaCase, RecordWildCards, OverloadedStrings, OverloadedLists, FlexibleContexts, ScopedTypeVariables #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Pattern (
  convertPat,  convertLPat, runPatternT,
  -- * Utility
  Refutability(..), refutability, isRefutable, isConstructor, isSoleConstructor,

  PatternSummary(..), patternSummary, multPatternSummary,
  isUnderscoreMultPattern,
  mutExcl, mutExcls,
  isCompleteMultiPattern,
) where

import Control.Lens hiding ((<|))

import Data.Maybe
import Data.Traversable
import Data.List.NonEmpty (toList)
import qualified Data.Text as T

import HsToRocq.Util.Monad
import Control.Monad.Trans.Maybe
import Control.Monad (foldM)
import Control.Monad.Writer
import Control.Monad.Except

import qualified Data.Map.Strict as M

import GHC hiding (Name, HsChar, HsString)
import qualified GHC

#if __GLASGOW_HASKELL__ >= 900
import GHC.Types.SourceText (il_value)
import qualified GHC.Utils.Outputable as GHC
#else
import BasicTypes (IntegralLit(..))
import qualified Outputable as GHC
#endif

import HsToRocq.Util.GHC.FastString

import HsToRocq.Util.GHC
import HsToRocq.Util.GHC.HsExpr
import HsToRocq.Util.GHC.HsTypes (selectorFieldOcc_)
#if __GLASGOW_HASKELL__ >= 806
import HsToRocq.Util.GHC.HsTypes (noExtCon)
#endif
import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util as Coq

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Literals

--------------------------------------------------------------------------------

convertPat :: (LocalConvMonad r m, MonadWriter [Term] m, MonadError Qualid m) => Pat GhcRn -> m Pattern
convertPat (WildPat PlaceHolder) =
  pure UnderscorePat

convertPat (GHC.VarPat NOEXTP (L _ x)) =
  QualidPat <$> var ExprNS x

convertPat (LazyPat NOEXTP p) = do
  p' <- convertLPat p
  _ <- refutability p'
  return p'

convertPat (GHC.AsPat NOEXTP x p) =
  Coq.AsPat <$> convertLPat p <*> var ExprNS (unLoc x)

convertPat (ParPat NOEXTP NOT_GHC_910(GHC_900(_)) p NOT_GHC_910(GHC_900(_))) =
  convertLPat p

convertPat (BangPat NOEXTP p) =
  convertLPat p

#if __GLASGOW_HASKELL__ >= 806
convertPat (ListPat _overloaded pats) =
#else
convertPat (ListPat pats PlaceHolder overloaded') | let overloaded = fmap snd overloaded' =
#endif
#if __GLASGOW_HASKELL__ >= 900
  foldr (App2Pat (Bare "cons")) (Coq.VarPat "nil") <$> traverse convertLPat pats
#else
  if maybe True isNoSyntaxExpr overloaded
  then foldr (App2Pat (Bare "cons")) (Coq.VarPat "nil") <$> traverse convertLPat pats
  else convUnsupported "overloaded list patterns"
#endif

#if __GLASGOW_HASKELL__ >= 806
convertPat (TuplePat _ pats _boxity) =
#else
-- TODO: Mark converted unboxed tuples specially?
convertPat (TuplePat pats _boxity _PlaceHolders) =
#endif
  foldl1 (App2Pat (Bare "pair")) <$> traverse convertLPat pats

#if __GLASGOW_HASKELL__ >= 900
convertPat (ConPat _ (L _ hsCon) conVariety) = do
#else
convertPat (ConPatIn (L _ hsCon) conVariety) = do
#endif
  con <- var ExprNS hsCon
  whenM (view $ edits.skippedConstructors.contains con) $ throwError con

  case conVariety of
    PrefixCon GHC_900(_) args ->
      ArgsPat con <$> traverse convertLPat args

    RecCon HsRecFields{..} ->
      let recPatUnsupported what = do
            hsConStr <- ghcPpr hsCon
            convUnsupported $  "using a record pattern for the "
                            ++ what ++ " constructor `" ++ T.unpack hsConStr ++ "'"

      in lookupConstructorFields con >>= \case
           Just (RecordFields conFields) -> do
             let defaultPat field | isJust rec_dotdot = QualidPat field
                                  | otherwise         = UnderscorePat

             patterns <- fmap M.fromList . for rec_flds $
#if __GLASGOW_HASKELL__ >= 900
               \(L _ (HsFieldBind _ (L _ occ) hsPat pun)) -> do
#else
               \(L _ (HsRecField (L _ occ) hsPat pun)) -> do
#endif
                           field <- var ExprNS (selectorFieldOcc_ occ)
                           pat   <- if pun
                                    then pure $ Coq.VarPat (qualidBase field)
                                    else convertLPat hsPat
                           pure (field, pat)
             pure . ArgsPat con
                  $ map (\field -> M.findWithDefault (defaultPat field) field patterns) conFields

           Just (NonRecordFields count)
             | null rec_flds && isNothing rec_dotdot ->
               pure . ArgsPat con $ replicate count UnderscorePat

             | otherwise ->
               recPatUnsupported "non-record"

           Nothing -> recPatUnsupported "unknown"

    InfixCon l r -> do
      App2Pat con <$> convertLPat l <*> convertLPat r

#if __GLASGOW_HASKELL__ < 900
convertPat (ConPatOut{}) =
  convUnsupported "[internal?] `ConPatOut' constructor"

convertPat (CoPat NOEXTP _ _ _) =
  convUnsupported "coercion patterns"
#endif

convertPat ViewPat{} =
  convUnsupported "view patterns"

convertPat (SplicePat NOEXTP _) =
  convUnsupported "pattern splices"

convertPat (LitPat NOEXTP lit) =
  case lit of
    GHC.HsChar   _ c       -> pure $ InScopePat (StringPat $ T.singleton c) "char"
    HsCharPrim   _ _       -> convUnsupported "`Char#' literal patterns"
    -- Rocq string patterns match its native string, whereas Haskell
    -- strings in the base model are lists of Char. Like numeric guards,
    -- an equality test preserves fall-through to later alternatives.
    GHC.HsString _ fs      -> do
      name <- gensym "str"
      Coq.VarPat name <$ tell ([mkInfix (Var name) "GHC.Base.==" (convertFastString fs)] :: [Term])
    HsStringPrim _ _       -> convUnsupported "`Addr#' literal patterns"
    HsInt        _ intl    -> convertIntegerPat "`Integer' literal patterns" (il_value intl)
    HsIntPrim    _ int     -> convertIntegerPat "`Integer' literal patterns" int
    HsWordPrim   _ _       -> convUnsupported "`Word#' literal patterns"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literal patterns"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literal patterns"
    HsInteger    _ int _ty -> convertIntegerPat "`Integer' literal patterns" int
    HsRat{}               -> convUnsupported "`Rational' literal patterns"
    HsFloatPrim  _ _       -> convUnsupported "`Float#' literal patterns"
    HsDoublePrim _ _       -> convUnsupported "`Double#' literal patterns"
#if __GLASGOW_HASKELL__ >= 910
    _                      -> convUnsupported $ "unhandled literal pattern: " ++ GHC.showPprUnsafe lit
#elif __GLASGOW_HASKELL__ >= 806
    XLit v -> noExtCon v
#endif

#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertPat (NPat _ (L _ (XOverLit v)) _negate _eq) = noExtCon v
#endif
#if __GLASGOW_HASKELL__ >= 806
convertPat (NPat _ (L _ OverLit{..}) _negate _eq) = -- And strings
#else
convertPat (NPat (L _ OverLit{..}) _negate _eq PlaceHolder) = -- And strings
#endif
  case ol_val of
    HsIntegral   intl     -> convertIntegerPat "integer literal patterns" (il_value intl)
    HsFractional _        -> convUnsupported "fractional literal patterns"
    HsIsString   _src str -> pure . StringPat $ fsToText str

convertPat NPlusKPat{} =
  convUnsupported "n+k-patterns"

convertPat SumPat{} =
  convUnsupported "sum type patterns"

#if __GLASGOW_HASKELL__ >= 806
-- GHC 9.10 uses SigPat (type-annotated patterns) in more places, including
-- derived instances. We strip the type annotation, treating it like ParPat
-- and BangPat — the type info is redundant since Coq infers types.
convertPat (SigPat NOEXTP p _) =
  convertLPat p
#if __GLASGOW_HASKELL__ >= 910
convertPat EmbTyPat{} =
  convUnsupported "embedded type patterns"
convertPat InvisPat{} =
  convUnsupported "invisible type argument patterns"
#endif
convertPat XPat{} =
  convUnsupported "`XPat' constructor"  -- Can't use noExtCon to dispatch this on GHC 8.8
#else
convertPat (PArrPat _ _) =
  convUnsupported "parallel array patterns"

convertPat (SigPatIn _ _) =
  convUnsupported "`SigPatIn' constructor"

convertPat (SigPatOut _ _) =
  convUnsupported "`SigPatOut' constructor"
#endif

--------------------------------------------------------------------------------

convertLPat :: (LocalConvMonad r m, MonadWriter [Term] m, MonadError Qualid m) => LPat GhcRn -> m Pattern
convertLPat = convertPat . unLoc

--------------------------------------------------------------------------------

runPatternT :: LocalConvMonad r m => WriterT [Term] (ExceptT Qualid m) a -> m (Either Qualid (a, [Term]))
runPatternT = runExceptT . runWriterT

--------------------------------------------------------------------------------

convertIntegerPat :: (LocalConvMonad r m, MonadWriter [Term] m)
                  => String -> Integer -> m Pattern
convertIntegerPat what hsInt = do
  var <- gensym "num"
  int <- either convUnsupported pure $ convertInteger what hsInt
  Coq.VarPat var <$ tell ([mkInfix (Var var) "GHC.Base.==" (App1 "GHC.Num.fromInteger" (Num int))] :: [Term])

-- Nothing:    Not a constructor
-- Just True:  Sole constructor
-- Just False: One of many constructors
isSoleConstructor :: ConversionMonad r m => Qualid -> m (Maybe Bool)
isSoleConstructor con = runMaybeT $ do
  ty    <- MaybeT $ lookupConstructorType con
  ctors <-          lookupConstructors ty
  pure $ length (fromMaybe [] ctors) == 1

data Refutability = Trivial (Maybe Qualid) -- Variables (with `Just`), underscore (with `Nothing`)
                  | SoleConstructor       -- (), (x,y)
                  | Refutable             -- Nothing, Right x, (3,_)
                  deriving (Eq, Ord, Show, Read)

isRefutable :: Refutability -> Bool
isRefutable Refutable = True
isRefutable _ = False

-- Module-local
constructorRefutability :: ConversionMonad r m => Qualid -> [Pattern] -> m Refutability
constructorRefutability con args =
  isSoleConstructor con >>= \case
    Nothing    -> pure Refutable -- Error
    Just True  -> maximum . (SoleConstructor :) <$> traverse refutability args
    Just False -> pure Refutable

refutability :: ConversionMonad r m => Pattern -> m Refutability
refutability (ArgsPat con args)         = constructorRefutability con args
refutability (ExplicitArgsPat con args) = constructorRefutability con (toList args)
refutability (InfixPat arg1 con arg2)   = constructorRefutability (Bare con) [arg1,arg2]
refutability (Coq.AsPat pat _)          = refutability pat
refutability (InScopePat _ _)           = pure Refutable -- TODO: Handle scopes
refutability (QualidPat name)           = isSoleConstructor name <&> \case
                                               Nothing    -> Trivial $ Just name
                                               Just True  -> SoleConstructor
                                               Just False -> Refutable
refutability UnderscorePat              = pure $ Trivial Nothing
refutability (NumPat _)                 = pure Refutable
refutability (StringPat _)              = pure Refutable
refutability (OrPats _)                 = pure Refutable -- TODO: Handle or-patterns?

-- This turns a Pattern into a summary that contains just enough information
-- to determine disjointness of patterns
--
-- It is ok to err on the side of OtherSummary.
-- For example, OrPatterns are considered OtherSummary
data PatternSummary = OtherSummary | ConApp Qualid [PatternSummary]
  deriving Show

patternSummary :: TypeInfoMonad m => Pattern -> m PatternSummary
patternSummary (ArgsPat con args)         = ConApp con <$> mapM patternSummary args
patternSummary (ExplicitArgsPat con args) = ConApp con <$> mapM patternSummary (toList args)
patternSummary InfixPat{}                 = pure OtherSummary
patternSummary (Coq.AsPat pat _)          = patternSummary pat
patternSummary (InScopePat pat _)         = patternSummary pat
patternSummary (QualidPat name)           = isConstructor name <&> \case
    True -> ConApp name []
    False -> OtherSummary
patternSummary UnderscorePat              = pure OtherSummary
patternSummary (NumPat _)                 = pure OtherSummary
patternSummary (StringPat _)              = pure OtherSummary
patternSummary (OrPats _)                 = pure OtherSummary

multPatternSummary :: TypeInfoMonad m => MultPattern -> m [PatternSummary]
multPatternSummary (MultPattern pats) = mapM patternSummary (toList pats)

mutExcls :: [PatternSummary] -> [PatternSummary] -> Bool
mutExcls pats1 pats2 = or $ zipWith mutExcl pats1 pats2

mutExcl :: PatternSummary -> PatternSummary -> Bool
mutExcl (ConApp con1 args1) (ConApp con2 args2)
    = con1 /= con2 || mutExcls args1 args2
mutExcl _ _ = False

-- A simple completeness checker. Traverses the list of patterns, and keep
-- tracks of all pattern summaries that we still need to match Internally, we
-- use OtherSummary as “everything yet has to match”
type Missing = [PatternSummary]
type Missings = [Missing]

isCompleteMultiPattern :: forall m. TypeInfoMonad m => [MultPattern] -> m Bool
-- Maybe an empty data type?
isCompleteMultiPattern [] = pure True
-- Reverse the list of patterns when checking for completeness. In Haskell more
-- general patterns follow specialized patterns and in particular the catch-all
-- clause is always last.
isCompleteMultiPattern mpats = null <$> goGroup (reverse mpats)
  where
    -- Initially, we miss everything
    initMissings = [[]]

    goGroup :: [MultPattern] -> m Missings
    goGroup = foldM goMP initMissings

    goMP :: Missings -> MultPattern -> m Missings
    goMP missings mpats = multPatternSummary mpats >>= goPatsSet missings

    goPatsSet :: Missings -> [PatternSummary] -> m Missings
    goPatsSet missingSet pats = concat <$> mapM (`gos` pats) missingSet

    -- Combinding an conjunction of patterns
    gos :: Missing -> [PatternSummary] -> m Missings
    gos _ [] = pure []
    gos [] pats = gos [OtherSummary] pats
    gos (m:missings) (p:pats) = do
        m' <- go m p
        missings' <- gos missings pats
        pure $ combineMissingsWith (:) m missings m' missings'

    -- A single pattern
    go :: PatternSummary -> PatternSummary -> m Missing
    -- The pattern handles all cases
    go _ OtherSummary = pure []
    -- The pattern applies only partially. Split the input and recurse.
    go OtherSummary p@(ConApp con _) =
        fromMaybe [] <$> runMaybeT (do
           ty    <- MaybeT $ lookupConstructorType con
           ctors <- MaybeT $ lookupConstructors ty
           -- Re-run the process with a separate Missing for each constructor
           lift $ concat <$> mapM (\ctor -> go (ConApp ctor []) p) ctors
        )
        -- What if we do not know this constructor? Just assume it is
        -- completeness for now
    go m@(ConApp con1 args1) (ConApp con2 args2)
        -- The pattern applies, so the missing is restricted
        -- to what’s left by the arguments, and what’s left to be done
        | con1 == con2 = (ConApp con1 `map`) <$> gos args1 args2
        -- The pattern does not apply, so the missing is unchanged
        | otherwise    = pure [m]

combineMissingsWith :: (a -> b -> c) -> a -> b -> [a] -> [b] -> [c]
combineMissingsWith f a b as bs = ((`f`b) <$> as) ++ ((a`f`) <$> bs)
-- this is the Applicative instance of Succs -- who would have thought
-- I wonder if the code above would be simpler when written with some sort
-- of SuccsT m

isUnderscoreMultPattern :: MultPattern -> Bool
isUnderscoreMultPattern (MultPattern pats) = all isUnderscoreRocq pats

isUnderscoreRocq :: Pattern -> Bool
isUnderscoreRocq UnderscorePat = True
isUnderscoreRocq _ = False
