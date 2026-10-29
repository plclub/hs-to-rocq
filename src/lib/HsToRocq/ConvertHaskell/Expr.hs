{-# LANGUAGE CPP,
             TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             ViewPatterns  #-}
-- GHC API compatibility shims (getLoc_, noLoc_, reLocA, conPatIn, unboundVarOcc)
-- live inside CPP blocks with version-dependent types; adding portable type
-- signatures across all supported GHC versions would be fragile.
{-# OPTIONS_GHC -Wno-missing-signatures #-}

#include "ghc-compat.h"

module HsToRocq.ConvertHaskell.Expr (
  convertTypedModuleBinding,
  convertMethodBinding,
  convertTypedModuleBindings,
  hsBindName,
  ) where

import Prelude hiding (Num())

import Control.Lens

import Control.Arrow ((&&&))
import Data.Bifunctor
import Data.Foldable
import Data.Function (on)
import HsToRocq.Util.Foldable
import Data.Functor (($>))
import Data.Traversable
import Data.Bitraversable
import HsToRocq.Util.Function
import Data.Maybe
import Data.Either
import Data.List (sortBy)
import HsToRocq.Util.List hiding (unsnoc)
import Data.List.NonEmpty (nonEmpty, NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import qualified HsToRocq.Util.List as NEL ((|>))
import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad (guard, replicateM, (<=<))
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.Writer
import Data.Monoid (Endo(..))

import HsToRocq.Util.Containers

import           Data.Set        (Set)
import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name, HsChar, HsString, AsPat)
import qualified GHC
-- GHC 9.0+ reorganized the module hierarchy; imports are CPP-gated by version.
-- GHC 9.0+ also replaced GHC's own exception handling with Control.Monad.Catch.
#if __GLASGOW_HASKELL__ >= 910
import GHC.Data.Bag (bagToList)
import GHC.Types.Name.Reader (mkOrig)
import GHC.Types.Basic (Origin(..), GenReason(..), DoPmc(..))
import GHC.Types.SourceText (IntegralLit(..), SourceText(..))
import GHC.Hs.Expr (XXExprGhcRn(..))
import qualified GHC.Utils.Outputable as GHC
import qualified Control.Monad.Catch as MC
#define ghandle MC.handle
#elif __GLASGOW_HASKELL__ >= 900
import GHC.Data.Bag (bagToList)
import GHC.Types.Name.Reader (mkOrig)
import GHC.Types.Basic (Origin(..))
import GHC.Types.SourceText (IntegralLit(..), SourceText(..))
import qualified GHC.Utils.Outputable as GHC
import qualified Control.Monad.Catch as MC
#define ghandle MC.handle
#else
import Bag
import BasicTypes
import RdrName
import qualified Outputable as GHC
#endif

import HsToRocq.Util.GHC.FastString
import HsToRocq.Util.GHC.Exception

import HsToRocq.Util.GHC
import HsToRocq.Util.GHC.Module
import HsToRocq.Util.GHC.Name hiding (Name)
import HsToRocq.Util.GHC.HsExpr
import HsToRocq.Util.GHC.HsTypes (selectorFieldOcc_, fieldOcc, noExtCon)
import HsToRocq.Rocq.Gallina as Coq
import HsToRocq.Rocq.Gallina.Util
import HsToRocq.Rocq.Gallina.UseTypeInBinders
import HsToRocq.Rocq.Subst
import HsToRocq.Rocq.Gallina.Rewrite as Coq
import HsToRocq.Rocq.FreeVars
import HsToRocq.Util.FVs (ErrOrVars(..))
import HsToRocq.Rocq.Pretty

import HsToRocq.Edits.Types
import HsToRocq.ConvertHaskell.TypeInfo
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables
import HsToRocq.ConvertHaskell.Definitions
import HsToRocq.ConvertHaskell.Literals
import HsToRocq.ConvertHaskell.HsType
import HsToRocq.ConvertHaskell.Pattern
import HsToRocq.ConvertHaskell.Sigs
import HsToRocq.ConvertHaskell.Axiomatize

import HsToRocq.ConvertHaskell.TypeEnv.Id

-- Compatibility shims: GHC 9.0+ uses LocatedAn (annotated locations) instead
-- of Located, and renames/restructures several pattern constructors.
-- These thin wrappers let the rest of the file use uniform names.
#if __GLASGOW_HASKELL__ >= 910
unboundVarOcc = id
getLoc_ x = getLocA x
noLoc_ x = noLocA x
reLocA (L l a) = L (noAnnSrcSpan l) a
conPatIn name = ConPat noExtField (noLocA name)
#elif __GLASGOW_HASKELL__ >= 900
unboundVarOcc = id
getLoc_ = getLocA
noLoc_ = noLocA
conPatIn = ConPat noExtField
#else
getLoc_ = getLoc
noLoc_ = noLoc
reLocA = id
conPatIn = ConPatIn
type LocatedAn x = Located
#endif

-- GHC 9.0+ changed SrcSpan so sortOn getLoc no longer works directly;
-- we compare the start SrcLoc of each binding's span instead.
compareSrcLoc :: SrcLoc -> SrcLoc -> Ordering
compareSrcLoc (UnhelpfulLoc _) (UnhelpfulLoc _) = EQ
compareSrcLoc (UnhelpfulLoc _) (RealSrcLoc _ _) = LT
compareSrcLoc (RealSrcLoc _ _) (UnhelpfulLoc _) = GT
compareSrcLoc (RealSrcLoc x _) (RealSrcLoc y _) = compare x y

--------------------------------------------------------------------------------

rewriteExpr :: ConversionMonad r m => Term -> m Term
rewriteExpr tm = do
  rws <- view (edits.rewrites)
  return $ Coq.rewrite rws tm

-- Module-local
ilInteger :: IntegralLit -> Integer
ilInteger IL{..} = (if il_neg then negate else id) il_value

-- Module-local
convertIntLiteral :: LocalConvMonad r m => String -> Integer -> m Term
convertIntLiteral what = either convUnsupported (pure . Num)
                         . convertInteger (what ++ " literals")

convertExpr :: LocalConvMonad r m => HsExpr GhcRn -> m Term
convertExpr hsExpr = convertExpr_ hsExpr >>= rewriteExpr

convertExpr_ :: forall r m. LocalConvMonad r m => HsExpr GhcRn -> m Term
convertExpr_ (HsVar NOEXTP (L _ x)) =
  Qualid <$> var ExprNS x

convertExpr_ (HsUnboundVar NOEXTP x) =
  Var <$> freeVar (unboundVarOcc x)

convertExpr_ HsOverLabel{} =
  convUnsupported "overloaded labels"

convertExpr_ (HsIPVar NOEXTP _) =
  convUnsupported "implicit parameters"

convertExpr_ (HsOverLit NOEXTP OverLit{..}) =
  case ol_val of
    HsIntegral   intl     -> App1 "GHC.Num.fromInteger" <$> convertIntLiteral "integer" (ilInteger intl)
    HsFractional fr       -> convertFractional fr
    HsIsString   _src str -> pure $ convertFastString str

convertExpr_ (HsLit NOEXTP lit) =
  case lit of
    GHC.HsChar   _ c       -> pure $ HsChar c
    HsCharPrim   _ _       -> convUnsupported "`Char#' literals"
    GHC.HsString _ fs      -> pure $ convertFastString fs
    HsStringPrim _ _       -> convUnsupported "`Addr#' literals"
    HsInt        _ intl    -> convertIntLiteral "`Int'" (ilInteger intl)
    HsIntPrim    _ int     -> convertIntLiteral "`IntPrim'" int
    HsWordPrim   _ _       -> convUnsupported "`Word#' literals"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literals"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literals"
    HsInteger    _ int _ty -> convertIntLiteral "`Integer'" int
    HsRat{}                -> convUnsupported "`Rational' literals"
    HsFloatPrim  _ _       -> convUnsupported "`Float#' literals"
    HsDoublePrim _ _       -> convUnsupported "`Double#' literals"
#if __GLASGOW_HASKELL__ >= 910
    _                      -> convUnsupported $ "unhandled literal type: " ++ GHC.showPprUnsafe lit
#elif __GLASGOW_HASKELL__ >= 806
    XLit v -> noExtCon v
#endif

-- GHC 9.10 merged HsLam and HsLamCase into a single HsLam constructor
-- with a LamAlt tag: LamSingle = ordinary lambda, LamCase/LamCases = \case.
#if __GLASGOW_HASKELL__ >= 910
convertExpr_ (HsLam NOEXTP LamSingle mg) =
  uncurry Fun <$> convertFunction [] mg

convertExpr_ (HsLam NOEXTP _ mg) = do
  skipPats <- views (edits.skippedCasePatterns) (S.map pure)
  uncurry Fun <$> convertFunction skipPats mg
#else
convertExpr_ (HsLam NOEXTP mg) =
  uncurry Fun <$> convertFunction [] mg -- We don't skip any equations in an ordinary lambda

convertExpr_ (HsLamCase NOEXTP GHC_900(_) mg) = do
  skipPats <- views (edits.skippedCasePatterns) (S.map pure)
  uncurry Fun <$> convertFunction skipPats mg
#endif

convertExpr_ (HsApp NOEXTP e1 e2) =
  App1 <$> convertLExpr e1 <*> convertLExpr e2

#if __GLASGOW_HASKELL__ >= 808
convertExpr_ (HsAppType NOEXTP e1 _) =
#elif __GLASGOW_HASKELL__ == 806
convertExpr_ (HsAppType _ e1) =
#else
convertExpr_ (HsAppType e1 _) =
#endif
  convertLExpr e1
--  convUnsupported "type applications"
--  SCW: just ignore them for now, and let the user figure it out.

#if __GLASGOW_HASKELL__ >= 806
convertExpr_ (OpApp _fixity el eop er) =
#else
convertExpr_ (OpApp el eop _fixity er) =
#endif
  case eop of
    L _ (HsVar NOEXTP (L _ hsOp)) -> do
      op  <- var ExprNS hsOp
      op' <- rewriteExpr $ Qualid op
      l   <- convertLExpr el
      r   <- convertLExpr er
      pure $ App2 op' l r
    _ ->
      convUnsupported "non-variable infix operators"

convertExpr_ (NegApp NOEXTP e1 _) =
  App1 <$> rewriteExpr "GHC.Num.negate" <*> convertLExpr e1

convertExpr_ (HsPar NOEXTP NOT_GHC_910(GHC_900(_)) e NOT_GHC_910(GHC_900(_))) =
  Parens <$> convertLExpr e

convertExpr_ (SectionL NOEXTP l opE) =
  convertSection (Just l) opE Nothing

convertExpr_ (SectionR NOEXTP opE r) =
  convertSection Nothing opE (Just r)

-- TODO: Mark converted unboxed tuples specially?
convertExpr_ (ExplicitTuple NOEXTP exprs _boxity) = do
  -- TODO A tuple constructor in the Gallina grammar?
  (tuple, args) <- runWriterT
                .  fmap (foldl1 . App2 $ "pair")
                .  for exprs $ NOT_GHC_900(unLoc <&>) \case
                     Present NOEXTP e -> lift $ convertLExpr e
                     Missing PlaceHolder ->
                       do arg <- lift (genqid "arg")
                          Qualid arg <$ tell [arg]
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
                     XTupArg v -> noExtCon v
#endif
  pure $ maybe id Fun (nonEmpty $ map (mkBinder Coq.Explicit . Ident) args) tuple

convertExpr_ (HsCase NOEXTP e mg) = do
  scrut    <- convertLExpr e
  skipPats <- views (edits.skippedCasePatterns) (S.map pure)
  bindIn "scrut" scrut $ \scrut -> convertMatchGroup skipPats [scrut] mg

-- GHC 9.0+ removed the optional SyntaxExpr from HsIf (overloaded if-then-else
-- is now handled via rebindable syntax / ExpandedThingRn instead).
#if __GLASGOW_HASKELL__ < 900
convertExpr_ (HsIf NOEXTP (Just (isNoSyntaxExpr -> False)) c t f) =
  convUnsupported "overloaded if-then-else"
#endif
convertExpr_ (HsIf NOEXTP NOT_GHC_900(_) c t f) =
  ifThenElse <*> pure SymmetricIf <*> convertLExpr c <*> convertLExpr t <*> convertLExpr f

convertExpr_ (HsMultiIf PlaceHolder lgrhsList) =
  convertLGRHSList [] lgrhsList patternFailure

convertExpr_ (HsLet NOEXTP NOT_GHC_910(GHC_900(_)) (NOT_GHC_900(L _) binds) NOT_GHC_910(GHC_900(_)) body) =
  convertLocalBinds binds $ convertLExpr body

#if __GLASGOW_HASKELL__ >= 806
convertExpr_ (HsDo _ sty (L _ stmts)) =
#else
convertExpr_ (HsDo sty (L _ stmts) PlaceHolder) =
#endif
  case sty of
    ListComp        -> convertListComprehension stmts
    -- GHC 9.0+ added a Maybe ModuleName arg to DoExpr/MDoExpr (for qualified do).
    DoExpr GHC_900(_) -> convertDoBlock stmts
    MDoExpr GHC_900(_) -> convUnsupported "`mdo' expressions"

    GhciStmtCtxt    -> convUnsupported "GHCi statement expressions"
    MonadComp       -> convUnsupported "monad comprehensions"
    -- GHC 9.0+ removed these statement contexts from HsStmtContext.
#if __GLASGOW_HASKELL__ < 900
    ArrowExpr       -> convUnsupported "arrow expressions"
    PatGuard _      -> convUnsupported "pattern guard expressions"
    ParStmtCtxt _   -> convUnsupported "parallel statement expressions"
    TransStmtCtxt _ -> convUnsupported "transform statement expressions"
#endif
#if __GLASGOW_HASKELL__ < 806
    PArrComp        -> convUnsupported "parallel array comprehensions"
#endif

-- GHC 9.0+ removed the optional SyntaxExpr from ExplicitList (same rationale
-- as HsIf above: overloaded lists use rebindable syntax).
#if __GLASGOW_HASKELL__ < 900
convertExpr_ (ExplicitList PlaceHolder (Just (isNoSyntaxExpr -> False)) exprs) =
  convUnsupported "overloaded lists"
#endif
convertExpr_ (ExplicitList PlaceHolder NOT_GHC_900(_) exprs) =
  foldr (App2 "cons") "nil" <$> traverse convertLExpr exprs

-- TODO: Unify with the `RecCon` case in `ConPatIn` for `convertPat` (in
-- `HsToRocq.ConvertHaskell.Pattern`)
#if __GLASGOW_HASKELL__ >= 806
convertExpr_ (RecordCon _ (L _ hsCon) HsRecFields{..}) = do
#else
convertExpr_ (RecordCon (L _ hsCon) PlaceHolder conExpr HsRecFields{..}) = do
  unless (isNoPostTcExpr conExpr) $
    convUnsupported "unexpected post-typechecker record constructor"
#endif

  let recConUnsupported what = do
        hsConStr <- ghcPpr hsCon
        convUnsupported $  "creating a record with the " ++ what
                        ++ " constructor `" ++ T.unpack hsConStr ++ "'"

  con <- var ExprNS hsCon

  lookupConstructorFields con >>= \case
    Just (RecordFields conFields) -> do
      let defaultVal field | isJust rec_dotdot = Qualid field
                           | otherwise         = missingValue

      vals <- fmap M.fromList . for rec_flds $
#if __GLASGOW_HASKELL__ >= 900
        \(L _ (HsFieldBind _ (L _ occ) hsVal pun)) -> do
#else
        \(L _ (HsRecField (L _ occ) hsVal pun)) -> do
#endif
                field <- var ExprNS (selectorFieldOcc_ occ)
                val   <- if pun
                         then pure $ Qualid field
                         else convertLExpr hsVal
                pure (field, val)
      pure . appList (Qualid con)
           $ map (\field -> PosArg $ M.findWithDefault (defaultVal field) field vals) conFields

    Just (NonRecordFields count)
      | null rec_flds && isNothing rec_dotdot ->
        pure . appList (Qualid con) $ replicate count (PosArg missingValue)

      | otherwise ->
        recConUnsupported "non-record"

    Nothing -> recConUnsupported "unknown"

-- GHC 9.10 split RecordUpd into OverloadedRecUpdFields (DuplicateRecordFields)
-- and RegularRecUpdFields. GHC 9.0 used Either for the same distinction.
#if __GLASGOW_HASKELL__ >= 910
convertExpr_ (RecordUpd _ _recVal (OverloadedRecUpdFields _ _)) = convUnsupported "overloaded record update"
convertExpr_ (RecordUpd _ recVal (RegularRecUpdFields _ fields)) = do
#elif __GLASGOW_HASKELL__ >= 900
convertExpr_ (RecordUpd _ recVal (Right fields)) = convUnsupported "record update (Right)"
convertExpr_ (RecordUpd _ recVal (Left fields)) = do
#elif __GLASGOW_HASKELL__ >= 806
convertExpr_ (RecordUpd _ recVal fields) = do
#else
convertExpr_ (RecordUpd recVal fields PlaceHolder PlaceHolder PlaceHolder PlaceHolder) = do
#endif
  updates <- fmap M.fromList . for fields $
#if __GLASGOW_HASKELL__ >= 900
             \(L _ (HsFieldBind _ (L _ lbl) rhs pun)) -> do
#else
             \(L _ (HsRecField (L _ lbl) rhs pun)) -> do
#endif
               field <- recordField lbl
               pure (field, if pun then Nothing else Just rhs)

  let updFields = M.keys updates
      prettyUpdFields what =
        let quote f = "`" ++ T.unpack (qualidToIdent f) ++ "'"
        in explainStrItems quote "no" "," "and" what (what ++ "s") updFields

  recType <- traverse lookupRecordFieldType updFields >>= \case
               Just (Just recType, []) -> pure recType
               Just (Nothing,      []) -> convUnsupported $ "invalid record update with " ++ prettyUpdFields "non-record-field"
               _                       -> convUnsupported $ "invalid mixed-data-type record updates with " ++ prettyUpdFields "the given field"
             . S.minView . S.fromList

  ctors :: [Qualid]  <- maybe (convUnsupported "invalid unknown record type") pure =<< lookupConstructors recType

  let loc x = reLocA (mkGeneralLocated "generated" x)
      toLPat_ :: Pat GhcRn -> LPat GhcRn
      toLPat_ = toLPat "generated"
      toHs = freshInternalName . T.unpack

  let partialUpdateError :: Qualid -> m (Match GhcRn (LHsExpr GhcRn))
      partialUpdateError con = do
        hsCon   <- toHs (qualidToIdent con)
        hsError <- toHs "GHC.Err.error"
        pure $ GHC.Match
#if __GLASGOW_HASKELL__ >= 910
          { m_ctxt = LamAlt LamSingle
#else
          { m_ctxt = LambdaExpr
#endif
          , m_pats   = [ toLPat_ . conPatIn (GHC_910(hsCon) NOT_GHC_910(loc hsCon))
                             . RecCon $ HsRecFields { rec_flds = []
                                                    , rec_dotdot = Nothing } ]
          , m_grhss  = GRHSs { grhssGRHSs = [ loc . GRHS GHC_900(noAnn)NOT_GHC_900(NOEXT) [] . loc $
                                              HsApp NOANNEXT
                                                    (loc . HsVar NOEXT . loc $ hsError)
                                                    (loc . HsLit NOANNEXT . GHC.HsString (SourceText "") $ fsLit "Partial record update") ]
                             , grhssLocalBinds = NOT_GHC_900(loc) (EmptyLocalBinds NOEXT)
#if __GLASGOW_HASKELL__ >= 900
                             , grhssExt = emptyComments
#elif __GLASGOW_HASKELL__ >= 806
                             , grhssExt = NOEXT
#endif
                             }
#if __GLASGOW_HASKELL__ >= 900
          , m_ext = noAnn
#elif __GLASGOW_HASKELL__ >= 806
          , m_ext = NOEXT
#endif
          }

  matches <- for ctors $ \con ->
    lookupConstructorFields con >>= \case
      Just (RecordFields fields) | all (`elem` fields) $ M.keysSet updates -> do
#if __GLASGOW_HASKELL__ >= 900
        let addFieldOcc field@HsFieldBind{hfbAnn = ann, hfbLHS = L s lbl} =
              let rdrLbl = mkOrig <$> nameModule <*> nameOccName $ lbl
                  l = noLocA (fieldOcc (L s rdrLbl) lbl) in
              field{ hfbAnn = ann, hfbLHS = l }
            useFields fields = HsRecFields { rec_flds   = map (fmap addFieldOcc) fields
                                           , rec_dotdot = Nothing }
#else
        let addFieldOcc :: HsRecField' GHC.Name arg -> HsRecField GhcRn arg
            addFieldOcc field@HsRecField{hsRecFieldLbl = L s lbl} =
              let rdrLbl = mkOrig <$> nameModule <*> nameOccName $ lbl
                  l = L s (fieldOcc (L s rdrLbl) lbl) in
              field{ hsRecFieldLbl = l }
            useFields fields = HsRecFields { rec_flds   = map (fmap addFieldOcc) fields
                                           , rec_dotdot = Nothing }
#endif
        (fieldPats, fieldVals) <- fmap (bimap useFields useFields . unzip) . for fields $ \field -> do
          fieldVar   <- gensym (qualidBase field)
          hsField    <- toHs (qualidToIdent field)
          hsFieldVar <- toHs fieldVar
#if __GLASGOW_HASKELL__ >= 900
          let mkField arg = loc $ HsFieldBind noAnn (loc hsField) arg False
#else
          let mkField arg = loc $ HsRecField { hsRecFieldLbl = loc hsField
                                             , hsRecFieldArg = arg
                                             , hsRecPun      = False }
#endif
          pure ( mkField . toLPat_ . GHC.VarPat NOEXT . loc $ hsFieldVar
               , mkField . fromMaybe (loc . HsVar NOEXT $ loc hsField) -- NOT `fieldVar` – this was punned
                         $ M.findWithDefault (Just . loc . HsVar NOEXT $ loc hsFieldVar) field updates )

        hsCon <- toHs (qualidToIdent con)
#if __GLASGOW_HASKELL__ >= 806
        let r = RecordCon NOEXT (loc hsCon) fieldVals
#else
        let r = RecordCon (loc hsCon) PlaceHolder noPostTcExpr fieldVals
#endif
#if __GLASGOW_HASKELL__ >= 910
        pure GHC.Match { m_ctxt   = LamAlt LamSingle
#else
        pure GHC.Match { m_ctxt   = LambdaExpr
#endif
                       , m_pats   = [ toLPat_ . conPatIn (GHC_910(hsCon) NOT_GHC_910(loc hsCon)) $ RecCon fieldPats ]
                       , m_grhss  = GRHSs { grhssGRHSs = [ loc . GRHS GHC_900(noAnn)NOT_GHC_900(NOEXT) [] . loc $ r ]
                                          , grhssLocalBinds = NOT_GHC_900(loc) (EmptyLocalBinds NOEXT)
#if __GLASGOW_HASKELL__ >= 900
                                          , grhssExt = emptyComments
#elif __GLASGOW_HASKELL__ >= 806
                                          , grhssExt = NOEXT
#endif
                                          }
#if __GLASGOW_HASKELL__ >= 900
                       , m_ext = noAnn
#elif __GLASGOW_HASKELL__ >= 806
                       , m_ext = NOEXT
#endif
                       }

      Just _ ->
        partialUpdateError con
      Nothing ->
        convUnsupported "invalid unknown constructor in record update"

  -- GHC 9.10: HsCase takes a HsMatchContext (CaseAlt here); MG.mg_ext is
  -- now Generated with Origin/DoPmc tags instead of a bare NoExtField.
#if __GLASGOW_HASKELL__ >= 910
  convertExpr . HsCase CaseAlt recVal $
    MG { mg_alts    = loc $ map loc matches
       , mg_ext     = Generated OtherExpansion SkipPmc }
#elif __GLASGOW_HASKELL__ >= 806
  convertExpr . HsCase NOEXT recVal $
    MG { mg_alts    = loc $ map loc matches
       , mg_ext     = NOEXT
       , mg_origin  = Generated }
#else
  convertExpr . HsCase recVal $
    MG { mg_alts    = loc $ map loc matches
       , mg_arg_tys = []
       , mg_res_ty  = PlaceHolder
       , mg_origin  = Generated }
#endif


#if __GLASGOW_HASKELL__ >= 808
convertExpr_ (ExprWithTySig NOEXTP e sigWcTy) = do
#elif __GLASGOW_HASKELL__ == 806
convertExpr_ (ExprWithTySig sigWcTy e) = do
#else
convertExpr_ (ExprWithTySig e sigWcTy) = do
#endif
  -- Keep expression type annotations only when the type has no free
  -- variables to quantify.  When there are free type variables (e.g.
  -- (id :: b -> b) producing (forall b, b -> b)), the quantifier
  -- changes the type and prevents Coq from instantiating implicit args.
  -- When there are none (e.g. coerce (bitraverse :: (a -> Identity b) -> ...)),
  -- the annotation is needed for disambiguation.
  expr <- convertLExpr e
  ty <- convertLHsSigWcType PreserveUnusedTyVars sigWcTy
  case ty of
    Forall _ _ -> pure expr
    _          -> pure $ HasType expr ty

convertExpr_ (ArithSeq _postTc _overloadedLists info) =
  -- TODO: Special-case infinite lists?
  -- TODO: `enumFrom{,Then}{,To}` is really…?
  -- TODO: Add Coq syntax sugar?  Something like
  --
  --     Notation "[ :: from        '..' ]"    := (enumFrom       from).
  --     Notation "[ :: from , next '..' ]"    := (enumFromThen   from next).
  --     Notation "[ :: from        '..' to ]" := (enumFromTo     from      to).
  --     Notation "[ :: from , next '..' to ]" := (enumFromThenTo from next to).
  --
  -- Only `'..'` doesn't work for some reason.
  case info of
    From       low           -> App1 "GHC.Enum.enumFrom"       <$> convertLExpr low
    FromThen   low next      -> App2 "GHC.Enum.enumFromThen"   <$> convertLExpr low <*> convertLExpr next
    FromTo     low      high -> App2 "GHC.Enum.enumFromTo"     <$> convertLExpr low                       <*> convertLExpr high
    FromThenTo low next high -> App3 "GHC.Enum.enumFromThenTo" <$> convertLExpr low <*> convertLExpr next <*> convertLExpr high

-- GHC 9.0+ removed many HsExpr constructors (HsRecFld, HsSCC, HsCoreAnn,
-- HsBracket, HsTick, HsWrap, etc.); their functionality moved to XExpr
-- extensions (ExpandedThingRn, HsPragE) or was restructured.
#if __GLASGOW_HASKELL__ >= 900
#else
convertExpr_ (HsRecFld NOEXTP fld) =
  Qualid <$> recordField fld

convertExpr_ (HsSCC NOEXTP _ _ e) =
  convertLExpr e

convertExpr_ (HsCoreAnn NOEXTP _ _ e) =
  convertLExpr e

convertExpr_ (HsBracket{}) =
  convUnsupported "Template Haskell brackets"

convertExpr_ (HsRnBracketOut{}) =
  convUnsupported "`HsRnBracketOut' constructor"

convertExpr_ (HsTcBracketOut{}) =
  convUnsupported "`HsTcBracketOut' constructor"

convertExpr_ (HsTickPragma NOEXTP _ _ _ e) =
  convertLExpr e

convertExpr_ (HsConLikeOut{}) =
  convUnsupported "`HsConLikeOut' constructor"

convertExpr_ (HsTick NOEXTP _ e) =
  convertLExpr e

convertExpr_ (HsBinTick NOEXTP _ _ e) =
  convertLExpr e

convertExpr_ (HsWrap{}) =
  convUnsupported "`HsWrap' constructor"
#endif

#if __GLASGOW_HASKELL__ < 910
convertExpr_ (HsSpliceE{}) =
  convUnsupported "Quasiquoters and Template Haskell splices"
#endif

convertExpr_ (HsProc{}) =
  convUnsupported "`proc' expressions"

convertExpr_ HsStatic{} =
  convUnsupported "static pointers"

convertExpr_ (ExplicitSum{}) =
  convUnsupported "`ExplicitSum' constructor"

#if __GLASGOW_HASKELL__ >= 806
#if __GLASGOW_HASKELL__ < 910
convertExpr_ (HsOverLit _ (XOverLit v)) = noExtCon v
#endif
#if __GLASGOW_HASKELL__ >= 910
-- GHC 9.10 replaced HsRecFld with HsRecSel and split TH/pragma/annotation
-- constructors. HsPragE subsumes HsSCC/HsCoreAnn/HsTickPragma.
convertExpr_ (HsRecSel _ fld) =
  Qualid <$> var ExprNS (foExt fld)
convertExpr_ (HsPragE _ _ e) =
  convertLExpr e
convertExpr_ HsGetField{} =
  convUnsupported "record dot syntax (HsGetField)"
convertExpr_ (HsProjection _ _) =
  convUnsupported "record projection syntax (HsProjection)"
convertExpr_ HsTypedBracket{} =
  convUnsupported "typed Template Haskell brackets"
convertExpr_ HsUntypedBracket{} =
  convUnsupported "untyped Template Haskell brackets"
convertExpr_ HsTypedSplice{} =
  convUnsupported "typed Template Haskell splices"
convertExpr_ HsUntypedSplice{} =
  convUnsupported "untyped Template Haskell splices"
convertExpr_ HsEmbTy{} =
  convUnsupported "embedded type expressions (RequiredTypeArguments)"
-- GHC 9.10 wraps rebindable-syntax and derived expressions in
-- ExpandedThingRn (original, expanded); we convert the expanded form.
-- PopErrCtxt is an error-context wrapper with no semantic content.
convertExpr_ (XExpr (ExpandedThingRn _ e)) = convertExpr e
convertExpr_ (XExpr (PopErrCtxt e)) = convertLExpr e
#elif __GLASGOW_HASKELL__ >= 900
convertExpr_ (XExpr (HsExpanded _ e)) = convertExpr e
#else
convertExpr_ (XExpr v) = noExtCon v
#endif
#else
convertExpr_ (HsAppTypeOut _ _) =
  convUnsupported "`HsAppTypeOut' constructor"

convertExpr_ (ExprWithTySigOut e sigWcTy) = do
  expr <- convertLExpr e
  ty <- convertLHsSigWcType PreserveUnusedTyVars sigWcTy
  case ty of
    Forall _ _ -> pure expr
    _          -> pure $ HasType expr ty

convertExpr_ (ExplicitPArr _ _) =
  convUnsupported "explicit parallel arrays"

convertExpr_ (PArrSeq _ _) =
  convUnsupported "parallel array arithmetic sequences"
#endif

#if __GLASGOW_HASKELL__ < 810
convertExpr_ HsArrApp{} =
  convUnsupported "arrow application command"

convertExpr_ HsArrForm{} =
  convUnsupported "arrow command formation"

convertExpr_ EWildPat{} =
  convUnsupported "wildcard pattern in expression"

convertExpr_ EAsPat{} =
  convUnsupported "as-pattern in expression"

convertExpr_ EViewPat{} =
  convUnsupported "view-pattern in expression"

convertExpr_ ELazyPat{} =
  convUnsupported "lazy pattern in expression"
#endif

--------------------------------------------------------------------------------

-- Module-local
convertSection :: LocalConvMonad r m => Maybe (LHsExpr GhcRn) -> LHsExpr GhcRn -> Maybe (LHsExpr GhcRn) -> m Term
convertSection  ml opE mr = do
  let -- We need this type signature, and I think it's because @let@ isn't being
      -- generalized.
      hs :: ConversionMonad r m => Qualid -> m (HsExpr GhcRn)
      hs  = fmap (HsVar NOEXT . reLocA . mkGeneralLocated "generated") . freshInternalName . T.unpack . qualidToIdent
      coq = mkBinder Coq.Explicit . Ident

  arg <- Bare <$> gensym "arg"
  let orArg = maybe (noLoc_ <$> hs arg) pure
  l <- orArg ml
  r <- orArg mr
#if __GLASGOW_HASKELL__ >= 806
  Fun [coq arg] <$> convertExpr (OpApp defaultFixity l opE r)
#else
  -- TODO RENAMER look up fixity?
  Fun [coq arg] <$> convertExpr (OpApp l opE defaultFixity r)
#endif

--------------------------------------------------------------------------------

convertLExpr :: LocalConvMonad r m => LHsExpr GhcRn -> m Term
convertLExpr = convertExpr . unLoc

--------------------------------------------------------------------------------

convertFunction :: LocalConvMonad r m
                => Set (NonEmpty NormalizedPattern)
                -> MatchGroup GhcRn (LHsExpr GhcRn)
                -> m (Binders, Term)
convertFunction _ mg | Just alt <- isTrivialMatch mg = convTrivialMatch alt
convertFunction skipEqns mg = do
  let n_args = matchGroupArity mg
  args <- replicateM n_args (genqid "arg") >>= maybe err pure . nonEmpty
  let argBinders = mkBinder Coq.Explicit . Ident <$> args
  match <- convertMatchGroup skipEqns (Qualid <$> args) mg
  pure (argBinders, match)
 where
   err = convUnsupported "convertFunction: Empty argument list"

isTrivialMatch :: MatchGroup GhcRn (LHsExpr GhcRn) -> Maybe (Match GhcRn (LHsExpr GhcRn))
isTrivialMatch (MG { mg_alts = L _ [L _ alt] }) = trivMatch alt where

  trivMatch :: Match GhcRn (LHsExpr GhcRn) -> Maybe (Match GhcRn (LHsExpr GhcRn))
  trivMatch alt = if all trivLPat (m_pats alt) then Just alt else Nothing

  trivPat :: Pat GhcRn -> Bool
  trivPat (GHC.WildPat _) = False
  trivPat (GHC.VarPat NOEXTP _)  = True
  trivPat (GHC.BangPat NOEXTP p) = trivLPat p
  trivPat (GHC.LazyPat NOEXTP p) = trivLPat p
  trivPat (GHC.ParPat  NOEXTP NOT_GHC_910(GHC_900(_)) p NOT_GHC_910(GHC_900(_))) = trivLPat p
  trivPat _                     = False

  trivLPat = trivPat . unLPat
isTrivialMatch _ = Nothing

-- TODO: Unify with `isTrivialMatch` to return a `Maybe (Binders, Term)`
convTrivialMatch ::  LocalConvMonad r m =>
  Match GhcRn (LHsExpr GhcRn) ->  m (Binders, Term)
convTrivialMatch alt = do
  (MultPattern pats, _, rhs) <- convertMatch alt
                                  <&> fromMaybe (error "internal error: convTrivialMatch: not a trivial match!")
  names <- mapM patToName pats
  let argBinders = mkBinder Explicit <$> names
  body <- rhs patternFailure
  return (argBinders, body)

patToName :: LocalConvMonad r m => Pattern -> m Name
patToName UnderscorePat    = pure UnderscoreName
patToName (QualidPat qid)  = pure $ Ident qid
patToName _                = convUnsupported "patToArg: not a trivial pat"

--------------------------------------------------------------------------------

isTrueLExpr :: GhcMonad m => LHsExpr GhcRn -> m Bool
isTrueLExpr (L _ (HsVar NOEXTP x))         = ((||) <$> (== "otherwise") <*> (== "True")) <$> ghcPpr x
#if __GLASGOW_HASKELL__ < 900
isTrueLExpr (L _ (HsTick NOEXTP _ e))      = isTrueLExpr e
isTrueLExpr (L _ (HsBinTick NOEXTP _ _ e)) = isTrueLExpr e
#endif
isTrueLExpr (L _ (HsPar NOEXTP NOT_GHC_910(GHC_900(_)) e NOT_GHC_910(GHC_900(_)))) = isTrueLExpr e
isTrueLExpr _                       = pure False

--------------------------------------------------------------------------------

-- TODO: Unify `buildTrivial` and `buildNontrivial`?
convertPatternBinding :: LocalConvMonad r m
                      => LPat GhcRn -> LHsExpr GhcRn
                      -> (Term -> (Term -> Term) -> m a)
                      -> (Term -> Qualid -> (Term -> Term -> Term) -> m a)
                      -> (Qualid -> m a)
                      -> Term
                      -> m a
convertPatternBinding hsPat hsExp buildTrivial buildNontrivial buildSkipped fallback =
  runPatternT (convertLPat hsPat) >>= \case
    Left  skipped       -> buildSkipped skipped
    Right (pat, guards) -> do
      exp <- convertLExpr hsExp
     
      ib <- ifThenElse
     
      refutability pat >>= \case
        Trivial tpat | null guards ->
          buildTrivial exp $ Fun [mkBinder Coq.Explicit $ maybe UnderscoreName Ident tpat]
     
        nontrivial -> do
          cont <- genqid "cont"
          arg  <- genqid "arg"
     
          -- TODO: Use SSReflect's `let:` in the `SoleConstructor` case?
          -- (Involves adding a constructor to `Term`.)
          let fallbackMatches
                | SoleConstructor <- nontrivial = []
                | otherwise                     = [ Equation [MultPattern [UnderscorePat]] fallback ]
              guarded tm | null guards = tm
                         | otherwise   = ib LinearIf (foldr1 (App2 "andb") guards) tm fallback
     
          buildNontrivial exp cont $ \body rest ->
            Let cont [mkBinder Coq.Explicit $ Ident arg] Nothing
                     (Coq.Match [MatchItem (Qualid arg) Nothing Nothing] Nothing $
                       Equation [MultPattern [pat]] (guarded rest) : fallbackMatches)
              body

convertDoBlock :: LocalConvMonad r m => [ExprLStmt GhcRn] -> m Term
convertDoBlock allStmts = do
    case fmap unLoc <$> unsnoc allStmts of
      Just (stmts, lastStmt -> Just e) -> foldMap (Endo . toExpr . unLoc) stmts `appEndo` convertLExpr e
      Just _                           -> convUnsupported "invalid malformed `do' block"
      Nothing                          -> convUnsupported "invalid empty `do' block"
  where
#if __GLASGOW_HASKELL__ >= 806
    lastStmt (BodyStmt _ e _ _) = Just e
#else
    lastStmt (BodyStmt e _ _ _) = Just e
#endif
    lastStmt (LastStmt NOEXTP e _ _) = Just e
    lastStmt _                  = Nothing

    toExpr x rest = toExpr_ x rest >>= rewriteExpr

#if __GLASGOW_HASKELL__ >= 806
    toExpr_ (BodyStmt _ e _bind _guard) rest =
#else
    toExpr_ (BodyStmt e _bind _guard _PlaceHolder) rest =
#endif
      monThen <$> convertLExpr e <*> rest

#if __GLASGOW_HASKELL__ >= 806
    toExpr_ (BindStmt _ pat exp NOT_GHC_900(_bind _fail)) rest =
#else
    toExpr_ (BindStmt pat exp _bind _fail PlaceHolder) rest =
#endif
      convertPatternBinding
        pat exp
        (\exp' fun          -> monBind exp' . fun <$> rest)
        (\exp' cont letCont -> letCont (monBind exp' (Qualid cont)) <$> rest)
        (\skipped           -> convUnsupported $
          "binding against the skipped constructor `" ++ showP skipped ++ "' in `do' notation")
        (missingValue `App1` HsString "Partial pattern match in `do' notation")

    toExpr_ (LetStmt NOEXTP (NOT_GHC_900(L _) binds)) rest =
      convertLocalBinds binds rest

    toExpr_ (RecStmt{}) _ =
      convUnsupported "`rec' statements in `do` blocks"

    toExpr_ _ _ =
      convUnsupported "impossibly fancy `do' block statements"

    monBind e1 = mkInfix e1 "GHC.Base.>>="
    monThen e1 = mkInfix e1 "GHC.Base.>>"

convertListComprehension :: LocalConvMonad r m => [ExprLStmt GhcRn] -> m Term
convertListComprehension allStmts = case fmap unLoc <$> unsnoc allStmts of
  Just (stmts, LastStmt NOEXTP e _applicativeDoInfo _returnInfo) ->
    foldMap (Endo . toExpr . unLoc) stmts `appEndo`
      (App2 (Var "cons") <$> convertLExpr e <*> pure (Var "nil"))
  Just _ ->
    convUnsupported "invalid malformed list comprehensions"
  Nothing ->
    convUnsupported "invalid empty list comprehension"
  where
#if __GLASGOW_HASKELL__ >= 806
    toExpr (BodyStmt _ e _bind _guard) rest =
#else
    toExpr (BodyStmt e _bind _guard _PlaceHolder) rest =
#endif
      isTrueLExpr e >>= \case
        True  -> rest
        False -> ifThenElse <*> pure LinearIf
                            <*> convertLExpr e
                            <*> rest
                            <*> pure (Var "nil")

    -- TODO: `concatMap` is really…?
#if __GLASGOW_HASKELL__ >= 806
    toExpr (BindStmt _ pat exp NOT_GHC_900(_bind _fail)) rest =
#else
    toExpr (BindStmt pat exp _bind _fail PlaceHolder) rest =
#endif
      convertPatternBinding
        pat exp
        (\exp' fun          -> App2 concatMapT <$> (fun <$> rest) <*> pure exp')
        (\exp' cont letCont -> letCont (App2 concatMapT (Qualid cont) exp') <$> rest)
        (\skipped           -> pure $ App1 (Qualid "GHC.Skip.nil_skipped") (String $ textP skipped))
        (Var "nil")
        -- `GHC.Skip.nil_skipped` always returns `[]`, but it has a note about
        -- what constructor was skipped.

    toExpr (LetStmt NOEXTP (NOT_GHC_900(L _) binds)) rest =
      convertLocalBinds binds rest

    toExpr _ _ =
      convUnsupported "impossibly fancy list comprehension conditions"

    concatMapT :: Term
    concatMapT = "Coq.Lists.List.flat_map"

--------------------------------------------------------------------------------

{-
  = ArgsPat Qualid (NE.NonEmpty Pattern)
  | ExplicitArgsPat Qualid (NE.NonEmpty Pattern)
  | InfixPat Pattern Op Pattern
  | AsPat Pattern Ident
  | InScopePat Pattern Ident
  | QualidPat Qualid
  | UnderscorePat
  | NumPat HsToRocq.Rocq.Gallina.Num
  | StringPat T.Text
  | OrPats (NE.NonEmpty OrPattern)
-}

-- This function, used by both convertMatchGroup for the various matches,
-- as well as in convertMatch for the various guarded RHS, implements
-- fall-though semantics, by binding each item to a jump point and passing
-- the right failure jump target to the prevoius item.
chainFallThroughs :: LocalConvMonad r m =>
    [Term -> m Term] -> -- The matches, in syntax order
    Term -> -- The final failure value
    m Term
chainFallThroughs cases failure = go (reverse cases) failure where
   go (m:ls) next_case = do
      this_match <- m next_case
      bindIn "j" this_match $ \failure -> go ls failure
   go [] failure = pure failure


-- A match group contains multiple alternatives, and each can have guards, and
-- there is fall-through semantics. But often we know that if one pattern fall-through,
-- then the next pattern will not match. In that case, we want to bind them in the same
-- match-with clause, in the hope of obtaining a full pattern match
--
-- The plan is:
-- * Convert each alternative individually into a pair of a pattern and a RHS.
--   The RHS is a (shallow) function that takes the fall-through target.
--   This is done by convertMatch
-- * Group patterns that are mutually exclusive, and put them in match-with clauses.
--   Add a catch-all case if that group is not complete already.
-- * Chain these groups.
convertMatchGroup :: LocalConvMonad r m
                  => Set (NonEmpty NormalizedPattern)
                  -> NonEmpty Term
                  -> MatchGroup GhcRn (LHsExpr GhcRn)
                  -> m Term
convertMatchGroup skipEqns args (MG { mg_alts = L _ alts }) = do
    allConvAlts <- traverse (convertMatch . unLoc) alts
    let convAlts = [alt | Just alt@(MultPattern pats, _, _) <- allConvAlts
                        , (normalizePattern <$> pats) `notElem` skipEqns ]
    -- TODO: Group
    convGroups <- groupMatches convAlts

    let scrut = args <&> \arg -> MatchItem arg Nothing Nothing
    let matches = buildMatch scrut <$> convGroups

    chainFallThroughs matches patternFailure
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertMatchGroup _ _ (XMatchGroup v) = noExtCon v
#endif

data HasGuard = HasGuard | HasNoGuard deriving (Eq, Ord, Enum, Bounded, Show, Read)

groupMatches :: forall r m a. ConversionMonad r m =>
    [(MultPattern, HasGuard, a)] -> m [[(MultPattern, a)]]
groupMatches pats = map (map snd) . go <$> mapM summarize pats
  where
    -- Gather some summary information on the alternatives
    --  - do they have guards
    --  - what is their PatternSummary
    summarize :: (MultPattern, HasGuard, a) -> m ([PatternSummary], HasGuard, (MultPattern, a))
    summarize (mp,hg,x) = do
        s <- multPatternSummary mp
        return (s,hg,(mp,x))

    go :: forall x. [([PatternSummary], HasGuard, x)] -> [[([PatternSummary], x)]]
    go [] = pure []
    go ((ps,hg,x):xs) = case go xs of
        -- Append to a group if it has no guard
        (g:gs) | HasNoGuard <- hg          -> ((ps,x):g)  : gs
        -- Append to a group, if mutually exclusive with all members
               | all (mutExcls ps . fst) g -> ((ps,x):g)  : gs
        -- Otherwise, start a new group
        gs                                 -> [(ps,x)]    : gs


convertMatch :: LocalConvMonad r m =>
    Match GhcRn (LHsExpr GhcRn) -> -- the match
    m (Maybe (MultPattern, HasGuard, Term -> m Term)) -- the pattern, hasGuards, the right-hand side
convertMatch GHC.Match{..} =
  runPatternT (   maybe (convUnsupported "no-pattern case arms") pure . nonEmpty
              =<< traverse convertLPat m_pats) <&> \case
    Left _skipped        -> Nothing
    Right (pats, guards) ->
      let extraGuards = map BoolGuard guards
          rhs = convertGRHSs extraGuards m_grhss
     
          hg | null extraGuards = hasGuards m_grhss
             | otherwise        = HasGuard
     
      in Just (MultPattern pats, hg, rhs)
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertMatch (XMatch v) = noExtCon v
#endif

buildMatch :: ConversionMonad r m =>
    NonEmpty MatchItem -> [(MultPattern, Term -> m Term)] -> Term -> m Term
-- This short-cuts wildcard matches (avoid introducing a match-with alltogether)
buildMatch _ [(pats,mkRhs)] failure
    | isUnderscoreMultPattern pats = mkRhs failure
buildMatch scruts eqns failure = do
    -- Pass the failure
    eqns' <- forM eqns $ \(pat,mkRhs) -> (pat,) <$> mkRhs failure
    is_complete <- isCompleteMultiPattern (map fst eqns')
    pure $ Coq.Match scruts Nothing $
      [ Equation [pats] rhs | (pats, rhs) <- eqns' ] ++
      [ Equation [MultPattern (UnderscorePat <$ scruts)] failure | not is_complete ]
    -- Only add a catch-all clause if the the patterns can fail


--------------------------------------------------------------------------------

hasGuards :: GRHSs GhcRn e -> HasGuard
hasGuards (GRHSs NOEXTP [ L _ (GRHS NOEXTP [] _) ] _) = HasNoGuard
hasGuards _                             = HasGuard

convertGRHS :: LocalConvMonad r m
            => [ConvertedGuard m]
            -> GRHS GhcRn (LHsExpr GhcRn)
            -> ExceptT Qualid m (Term -> m Term)
convertGRHS extraGuards (GRHS NOEXTP gs rhs) = do
  convGuards <- (extraGuards ++) <$> convertGuard gs
  rhs <- convertLExpr rhs
  pure $ \failure -> guardTerm convGuards rhs failure
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertGRHS _ (XGRHS v) = noExtCon v
#endif

convertLGRHSList :: LocalConvMonad r m
                 => [ConvertedGuard m]
                 -> [LGRHS GhcRn (LHsExpr GhcRn)]
                 -> Term
                 -> m Term
convertLGRHSList extraGuards lgrhs failure = do
    let rhss = unLoc <$> lgrhs
    convRhss <- rights <$> traverse (runExceptT . convertGRHS extraGuards) rhss
    chainFallThroughs convRhss failure

convertGRHSs :: LocalConvMonad r m
             => [ConvertedGuard m]
             -> GRHSs GhcRn (LHsExpr GhcRn)
             -> Term
             -> m Term
convertGRHSs extraGuards GRHSs{..} failure =
    convertLocalBinds (NOT_GHC_900(unLoc) grhssLocalBinds) $
      convertLGRHSList extraGuards grhssGRHSs failure
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertGRHSs _ (XGRHSs v) _ = noExtCon v
#endif

--------------------------------------------------------------------------------

data ConvertedGuard m = OtherwiseGuard
                      | BoolGuard      Term
                      | PatternGuard   Pattern Term
                      | LetGuard       (m Term -> m Term)

convertGuard :: LocalConvMonad r m => [GuardLStmt GhcRn] -> ExceptT Qualid m [ConvertedGuard m]
convertGuard [] = pure []
convertGuard gs = collapseGuards <$> traverse (toCond . unLoc) gs where
#if __GLASGOW_HASKELL__ >= 806
  toCond (BodyStmt _ e _bind _guard) =
#else
  toCond (BodyStmt e _bind _guard _PlaceHolder) =
#endif
    isTrueLExpr e >>= \case
      True  -> pure [OtherwiseGuard]
      False -> (:[]) . BoolGuard <$> convertLExpr e
  toCond (LetStmt NOEXTP (NOT_GHC_900(L _) binds)) =
    pure . (:[]) . LetGuard $ convertLocalBinds binds
#if __GLASGOW_HASKELL__ >= 900
  toCond (BindStmt _ pat exp) = do
#elif __GLASGOW_HASKELL__ >= 806
  toCond (BindStmt _ pat exp _bind _fail) = do
#else
  toCond (BindStmt pat exp _bind _fail PlaceHolder) = do
#endif
    (pat', guards) <- runWriterT (convertLPat pat)
    exp'           <- convertLExpr exp
    pure $ PatternGuard pat' exp' : map BoolGuard guards
  toCond _ =
    convUnsupported "impossibly fancy guards"

  -- We optimize the code a bit, and combine
  -- successive boolean guards with andb
  collapseGuards = foldr addGuard [] . concat

  -- TODO: Add multi-pattern-guard case
  addGuard g [] =
    [g]
  addGuard (BoolGuard cond') (BoolGuard cond : gs) =
    BoolGuard (App2 (Var "andb") cond' cond) : gs
  addGuard g' (g:gs) =
    g':g:gs


-- Returns a function waiting for the "else case"
guardTerm :: LocalConvMonad r m =>
    [ConvertedGuard m] ->
    Term -> -- The guarded expression
    Term -> -- the failure expression
    m Term
guardTerm gs rhs failure = go gs where
  go [] =
    pure rhs
  go (OtherwiseGuard : gs) =
    go gs

  -- A little innocent but useful hack: Detect the pattern
  --     | foo `seq` False = …
  -- And hard-code that it fails
  go (BoolGuard (App2 "GHC.Prim.seq" _ p) : gs) = go (BoolGuard p : gs)
  go (BoolGuard "false" : _) = pure failure

  go (BoolGuard cond : gs) =
    ifThenElse <*> pure LinearIf <*> pure cond <*> go gs <*> pure failure
  go (PatternGuard pat exp : gs) = do
    guarded' <- go gs
    ref <- refutability pat
    let fallback = [ Equation [MultPattern [UnderscorePat]] failure
                   | isRefutable ref ]
    pure $ Coq.Match [MatchItem exp Nothing Nothing] Nothing
                     (Equation [MultPattern [pat]] guarded' : fallback)
  go (LetGuard bind : gs) =
    bind $ go gs

--------------------------------------------------------------------------------

-- Does not detect recursion/introduce `fix`
convertTypedBinding :: LocalConvMonad r m => Maybe Term -> HsBind GhcRn -> m (Maybe ConvertedBinding)
convertTypedBinding _convHsTy VarBind{}     = convUnsupported "[internal] `VarBind'"
#if __GLASGOW_HASKELL__ >= 900
#else
convertTypedBinding _convHsTy AbsBinds{}    = convUnsupported "[internal?] `AbsBinds'"
#endif
convertTypedBinding _convHsTy PatSynBind{}  = convUnsupported "pattern synonym bindings"
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertTypedBinding _ (XHsBindsLR v) = noExtCon v
#endif
convertTypedBinding _convHsTy PatBind{..}   = do -- TODO use `_convHsTy`?
  -- TODO: Respect `skipped'?
  -- TODO: what if we need to rename this definition? (i.e. for a class member)
  ax <- view currentModuleAxiomatized
  if ax
    then
      liftIO $ Nothing <$ putStrLn "skipping a pattern binding in an axiomatized module" -- TODO: FIX HACK
      -- convUnsupported "pattern bindings in axiomatized modules"
    else
      runPatternT (convertLPat pat_lhs) >>= \case
        Left  _skipped      -> pure Nothing
        Right (pat, guards) -> Just . ConvertedPatternBinding pat <$> convertGRHSs (map BoolGuard guards) pat_rhs patternFailure
convertTypedBinding convHsTy FunBind{..}   = do
    name <- var ExprNS (unLoc fun_id)
    
    -- Skip it?  Axiomatize it?
    definitionTask name >>= \case
      SkipIt ->
        pure . Just $ SkippedBinding name
      
      RedefineIt def ->
        pure . Just $ RedefinedBinding name def
      
      AxiomatizeIt axMode ->
        let missingType = case axMode of
              SpecificAxiomatize -> convUnsupported "axiomatizing definitions without type signatures"
              GeneralAxiomatize  -> pure bottomType
        in Just . ConvertedAxiomBinding name <$> maybe missingType pure convHsTy
      
      TranslateIt -> do
        let (tvs, coqTy) =
              -- The @forall@ed arguments need to be brought into scope
              let peelForall (Forall tvs body) = first (NEL.toList tvs ++) $ peelForall body
                  peelForall ty                = ([], ty)
              in maybe ([], Nothing) (second Just . peelForall) convHsTy
              -- in maybe ([], Nothing) (second Just . peelForall) (Just $ Qualid $ Bare "test")


        let tryCollapseLet defn = do
              view (edits.collapsedLets.contains name) >>= \case
                True  -> collapseLet name defn
                           & maybe (convUnsupported "collapsing non-`let x=… in x` lets") pure
                False -> pure defn
        
        defn <-
          tryCollapseLet =<<
            if all (null . m_pats . unLoc) . unLoc $ mg_alts fun_matches
            then case unLoc $ mg_alts fun_matches of
                   [L _ (GHC.Match NOEXTP _ [] grhss)] -> convertGRHSs [] grhss patternFailure
                   _ -> convUnsupported "malformed multi-match variable definitions"
            else do
              skipEqns <- view $ edits.skippedEquations.at name.non mempty
              uncurry Fun <$> convertFunction skipEqns fun_matches

        addScope <- maybe id (flip InScope) <$> view (edits.additionalScopes.at (SPValue, name))
        
        pure . Just . ConvertedDefinitionBinding $ ConvertedDefinition name tvs coqTy (addScope defn)

collapseLet :: Qualid -> Term -> Maybe Term
collapseLet outer (Let x args _oty defn (Qualid x')) | x == x' =
  Just . maybeFun args $ case defn of
    Fix (FixOne (FixBody f args' _mord _oty body)) -> Fun args' $ subst1 f (Qualid outer) body
    _                                              -> defn
collapseLet _ _ =
  Nothing

wfFix :: ConversionMonad r m => TerminationArgument -> FixBody -> m Term
wfFix Deferred (FixBody ident argBinders Nothing Nothing rhs)
 = pure $ App1 (Qualid deferredFixN) $ Fun (mkBinder Explicit (Ident ident) NEL.<| argBinders ) rhs
  where
    deferredFixN = qualidMapBase (<> T.pack (show (NEL.length argBinders)))
        "HsToRocq.DeferredFix.deferredFix"

wfFix (WellFoundedTA order) (FixBody ident argBinders Nothing Nothing rhs)
 = do (rel, measure) <- case order of
        MeasureOrder_ measure Nothing    -> pure ("Coq.Init.Peano.lt", measure)
        MeasureOrder_ measure (Just rel) -> pure (rel, measure)
        WFOrder_ rel arg                 -> pure (rel, Qualid arg)
      pure . appList (Qualid wfFixN) $ map PosArg
        [ rel
        , Fun argBinders measure
        , Underscore
        , Fun (argBinders NEL.|> mkBinder Explicit (Ident ident)) rhs
        ]
  where
    wfFixN = qualidMapBase (<> T.pack (show (NEL.length argBinders)))
        "HsToRocq.Wf.wfFix"

wfFix Corecursive fb = pure . Cofix $ FixOne fb

wfFix StructOrderTA{} (FixBody ident _ _ _ _) = convUnsupportedIn
  "well-founded recursion does not include structural recursion"
  "fixpoint" (showP ident)

wfFix _ fb = convUnsupportedIn "well-founded recursion cannot handle annotations or types"
                               "fixpoint"
                               (showP $ fb^.fixBodyName)

--------------------------------------------------------------------------------

-- find the first name in a pattern binding
patBindName :: ConversionMonad r m => Pat GhcRn -> m Qualid
patBindName p = case p of
  WildPat _ -> convUnsupported' "no name in binding pattern"
  GHC.VarPat NOEXTP (L _ hsName)  -> var ExprNS hsName
  LazyPat NOEXTP p -> lpatBindName p
  GHC.AsPat NOEXTP (L _ hsName) _ -> var ExprNS hsName
  ParPat NOEXTP NOT_GHC_910(GHC_900(_)) p NOT_GHC_910(GHC_900(_)) -> lpatBindName p
  BangPat NOEXTP p -> lpatBindName p
#if __GLASGOW_HASKELL__ >= 806
  ListPat _ (p:_) -> lpatBindName p
  TuplePat _ (p:_) _ -> lpatBindName p
#else
  ListPat (p:_) _ _ -> lpatBindName p
  TuplePat (p:_) _ _ -> lpatBindName p
#endif
  _ -> convUnsupported' ("Cannot find name in pattern: " ++  GHC.showSDocUnsafe (GHC.ppr p))

lpatBindName :: ConversionMonad r m => LPat GhcRn -> m Qualid
lpatBindName = patBindName . unLPat

unLPat :: LPat GhcRn -> Pat GhcRn
toLPat :: String -> Pat GhcRn -> LPat GhcRn
#if __GLASGOW_HASKELL__ == 808
unLPat = \case (XPat (L _ p)) -> p ; p -> p
toLPat _ = id
#else
unLPat = unLoc
toLPat = (fmap . fmap) reLocA mkGeneralLocated
#endif

hsBindName :: ConversionMonad r m => HsBind GhcRn -> m Qualid
hsBindName defn = case defn of
    FunBind{fun_id = L _ hsName} -> var ExprNS hsName
    PatBind{pat_lhs = p} -> lpatBindName p

    _ -> convUnsupported' ( "non-function top level bindings: " ++ GHC.showSDocUnsafe (GHC.ppr defn))

-- | Warn and immediately return 'Nothing' for unsupported top-level bindings.
withHsBindName
  :: ConversionMonad r m => HsBind GhcRn -> (Qualid -> m (Maybe a)) -> m (Maybe a)
withHsBindName b continue = case b of
    FunBind{fun_id = L _ hsName} -> var ExprNS hsName >>= continue
    PatBind{pat_lhs = p} ->
      warnConvUnsupported' (getLoc_ p) "top-level pattern binding" $> Nothing
    PatSynBind NOEXTP PSB{psb_id = i} ->
      warnConvUnsupported' (getLoc_ i) "pattern synonym" $> Nothing
    VarBind{} -> convUnsupported' "[internal] `VarBind' can't be a top-level binding"
#if __GLASGOW_HASKELL__ < 900
    AbsBinds{} -> convUnsupported' "[internal] `AbsBinds' can't be a top-level binding"
#endif
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
    PatSynBind NOEXTP (XPatSynBind v) -> noExtCon v
    XHsBindsLR v -> noExtCon v
#endif

-- This is where we switch from the global monad to the local monad
convertTypedModuleBinding :: ConversionMonad r m => Maybe Term -> HsBind GhcRn -> m (Maybe ConvertedBinding)
convertTypedModuleBinding ty defn =
  withHsBindName defn $ \name ->
    withCurrentDefinition name $ convertTypedBinding ty defn

convertTypedModuleBindings :: ConversionMonad r m
                           => [LHsBind GhcRn]
                           -> Map Qualid Signature
                           -> (ConvertedBinding -> m a)
                           -> Maybe (HsBind GhcRn -> GhcException -> m a)
                           -> m [a]
convertTypedModuleBindings = convertMultipleBindings convertTypedModuleBinding

-- | A variant of convertTypedModuleBinding that ignores the name in the HsBind
-- and uses the provided one instead
--
-- It also does not allow skipping or axiomatization, does not create fixpoints,
-- does not support a type, and always returns a binding (or fails with
-- convUnsupported).
--
-- It does, however, support redefinition.
convertMethodBinding :: ConversionMonad r m => Qualid -> HsBind GhcRn -> m ConvertedBinding
convertMethodBinding name VarBind{}     = convUnsupportedIn "[internal] `VarBind'"     "method" (showP name)
#if __GLASGOW_HASKELL__ >= 900
#else
convertMethodBinding name AbsBinds{}    = convUnsupportedIn "[internal?] `AbsBinds'"   "method" (showP name)
#endif
convertMethodBinding name PatSynBind{}  = convUnsupportedIn "pattern synonym bindings" "method" (showP name)
convertMethodBinding name PatBind{}     = convUnsupportedIn "pattern bindings"         "method" (showP name)
convertMethodBinding name FunBind{..}   = withCurrentDefinition name $ do
  definitionTask name >>= \case
    SkipIt ->
      convUnsupported "skipping instance method definitions (without `skip method')"
    RedefineIt def ->
      pure $ RedefinedBinding name def
    AxiomatizeIt _ ->
      convUnsupported "axiomatizing instance method definitions"
    TranslateIt -> do
      defn <-
        if all (null . m_pats . unLoc) . unLoc $ mg_alts fun_matches
        then case unLoc $ mg_alts fun_matches of
               [L _ (GHC.Match NOEXTP _ [] grhss)] -> convertGRHSs [] grhss patternFailure
               _ -> convUnsupported "malformed multi-match variable definitions"
        else do
          skipEqns <- view $ edits.skippedEquations.at name.non mempty
          uncurry Fun <$> convertFunction skipEqns fun_matches
      pure $ ConvertedDefinitionBinding $ ConvertedDefinition name [] Nothing defn
#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 910
convertMethodBinding _ (XHsBindsLR v) = noExtCon v
#endif

convertTypedBindings :: LocalConvMonad r m
                     => [LHsBind GhcRn] -> Map Qualid Signature
                     -> (ConvertedBinding -> m a)
                     -> Maybe (HsBind GhcRn -> GhcException -> m a)
                     -> m [a]
convertTypedBindings = convertMultipleBindings convertTypedBinding

convertMultipleBindings :: ConversionMonad r m
                        => (Maybe Term -> HsBind GhcRn -> m (Maybe ConvertedBinding))
                        -> [LHsBind GhcRn]
                        -> Map Qualid Signature
                        -> (ConvertedBinding -> m a)
                        -> Maybe (HsBind GhcRn -> GhcException -> m a)
                        -> m [a]
convertMultipleBindings convertSingleBinding defns0 sigs build mhandler =
  let defns = sortBy (compareSrcLoc `on` (srcSpanStart . getLoc_)) defns0
      (handler, wrap) = case mhandler of
        Just handler -> ( uncurry handler
                        , \defn -> ghandle $ pure . Left . (defn,))
        Nothing      -> ( const $ throwProgramError
          "INTERNAL ERROR: convertMultipleBindings tried to both handle and ignore an exception"
                            -- Safe because the only place `Left' is introduced
                            -- is in the previous case branch
                        , const id )
  in traverse (either handler build) <=< addRecursion <=< fmap catMaybes . for defns $ \(L _ defn) ->
       -- 'MaybeT' is responsible for handling the skipped definitions, and
       -- nothing else
       runMaybeT . wrap defn . fmap Right $ do
         ty <- case defn of
                 FunBind{fun_id = L _ hsName} -> do
                   coqName <- var ExprNS hsName
                   mod <- view (currentModule.modDetails)
                   env <- withCurrentDefinition coqName $ idEnvOfModDetails mod
                   case convertedIdType coqName env of
                     Nothing -> fmap sigType <$> lookupSig coqName sigs
                     t       -> view (edits.replacedTypes.at coqName) >>= \case
                       Nothing -> pure t
                       _       -> fmap sigType <$> lookupSig coqName sigs
                 _ -> pure Nothing
         MaybeT $ convertSingleBinding ty defn

-- ALMOST a 'ConvertedDefinition', but:
--   (a) It's guaranteed to have arguments; and
--   (b) We store two types: the result type AFTER the argument types
--       ('rdResultType'), and the full type including the argument types
--       ('rdFullType')
data RecDef = RecDef { rdName       :: !Qualid
                     , rdArgs       :: !Binders
                     , rdStruct     :: !(Maybe Order)
                     , rdResultType :: !(Maybe Term)
                     , rdFullType   :: !(Maybe Term)
                     , rdBody       :: !Term }
            deriving (Eq, Ord, Show, Read)

-- CURRENT IMPLEMENTATION: If we can't move the type to arguments, then:
--   * If it was translated, fail-safe, and translate without the type
--   * If it was specified, abort
-- We can't unilaterally abort unless we can change type signatures.

rdToFixBody :: RecDef -> FixBody
rdToFixBody RecDef{..} = FixBody rdName rdArgs rdStruct rdResultType rdBody

rdToLet :: RecDef -> Term -> Term
rdToLet RecDef{..} = Let rdName (toList rdArgs) rdResultType rdBody

rdStripResultType :: RecDef -> RecDef
rdStripResultType rd = rd{rdResultType = Nothing}

splitInlinesWith :: Foldable f => Set Qualid -> f RecDef -> Maybe (Map Qualid RecDef, NonEmpty RecDef)
splitInlinesWith inlines =
  bitraverse (pure . fold) nonEmpty .: mapPartitionEithers $ \rd@RecDef{..} ->
    if rdName `elem` inlines
    then Left $ M.singleton rdName rd
    else Right rd

data RecType = Standalone | Mutual deriving (Eq, Ord, Enum, Bounded, Show, Read)

mutualRecursionInlining :: ConversionMonad r m => NonEmpty RecDef -> m (Map Qualid (RecType, RecDef))
mutualRecursionInlining mutGroup = do
  -- TODO: Names of recursive functions in inlining errors
  
  inlines      <- view $ edits.inlinedMutuals
  (lets, recs) <- splitInlinesWith inlines mutGroup
                    & maybe (editFailure "can't inline every function in a mutually-recursive group") pure
  
  let rdFVs   = getFreeVars . rdBody
      letUses = rdFVs <$> lets
      letDeps = transitiveClosure Reflexive letUses

  orderedLets <- for (topoSortEnvironmentWith id letUses) $ \case
    solo :| []  -> pure solo
    _    :| _:_ -> editFailure "recursion forbidden amongst inlined mutually-recursive functions"
  
  let recMap = flip foldMap recs $ \rd ->
        let neededLets  = foldMap (M.findWithDefault mempty ?? letDeps) $ rdFVs rd
            inlinedDeps = filter (`elem` neededLets) orderedLets
        in M.singleton (rdName rd)
                       (Mutual, rd{rdBody = foldr (rdToLet . (lets M.!)) (rdBody rd) inlinedDeps})
  
  pure $ ((Standalone,) <$> lets) <> recMap

addRecursion :: ConversionMonad r m => [Either e ConvertedBinding] -> m [Either e ConvertedBinding]
addRecursion eBindings = do
  fixedBindings <-  M.fromList . fmap (view convDefName &&& id) . foldMap toList
                <$> traverse fixConnComp (stronglyConnCompNE
                      [ (cd, cd^.convDefName, S.toAscList . getFreeVars $ cd^.convDefBody)
                      | Right (ConvertedDefinitionBinding cd) <- eBindings ])
      
  pure . topoSortByVariablesBy ErrOrVars M.empty . flip map eBindings $ \case
    Right (ConvertedDefinitionBinding cd) -> case M.lookup (cd^.convDefName) fixedBindings of
      Just cd' -> Right $ ConvertedDefinitionBinding cd'
      Nothing  -> error "INTERNAL ERROR: lost track of converted definition during mutual recursion check"
    untouched ->
      untouched
  where
    fixConnComp (cd :| []) | cd^.convDefName `notElem` getFreeVars (cd^.convDefBody) =
      pure $ cd :| []
    fixConnComp cds = do
      (commonArgs, cds) <- splitArgs cds
      tbodies <- for cds fixConvertedDefinition

      let bodies = fst <$> tbodies

      let nonstructural = listToMaybe [t | (_, Just t) <- toList tbodies, isNonstructural t]
          isNonstructural (StructOrderTA _) = False
          isNonstructural _ = True

      let getInfo = fmap $ rdName &&& rdFullType
      
      (fixFor, recInfos, extraDefs) <- case (nonstructural, bodies) of
        (Just order, body1 :| []) -> do
          fixed <- wfFix order . rdToFixBody $ rdStripResultType body1
          pure (const fixed, getInfo bodies, [])
        
        (Just _, _ :| _ : _) ->
          convUnsupportedIn "non-structural mutual recursion" "definitions"
                            (explainStrItems (showP . rdName) "" "," "and" "" "" bodies)
        
        (Nothing, body1 :| []) ->
          pure (const . Fix . FixOne $ rdToFixBody body1, getInfo bodies, [])
        
        (Nothing, _ :| _ : _) -> do
          mutRecInfo <- mutualRecursionInlining bodies
          let (recs', lets) = flip mapPartitionEithers cds $ \cd ->
                case M.lookup (cd^.convDefName) mutRecInfo of
                  Just (Standalone, _)  -> Right $ cd & convDefArgs %~ (commonArgs ++)
                  Just (Mutual,     rd) -> Left rd
                  Nothing               -> error "INTERNAL ERROR: lost track of mutually-recursive function"
              recs = fromMaybe (error "INTERNAL ERROR: \
                                      \all mutually-recursive functions in this group vanished!")
                   $ nonEmpty recs'
          
          let fixFor = case recs of
                body1 :| []              ->
                  const . Fix . FixOne $ rdToFixBody body1
                body1 :| body2 : bodies' ->
                  Fix . FixMany (rdToFixBody body1) (rdToFixBody <$> (body2 :| bodies'))
          
          pure (fixFor, getInfo recs, lets)
          
      let recDefs = recInfos <&> \(name,mty) ->
            ConvertedDefinition { _convDefName = name
                                , _convDefArgs = commonArgs
                                , _convDefType = mty
                                , _convDefBody = fixFor name }
      pure $ recDefs ++> extraDefs

fixConvertedDefinition ::
  ConversionMonad r m => ConvertedDefinition -> m (RecDef, Maybe TerminationArgument)
fixConvertedDefinition ConvertedDefinition{_convDefBody = Fun args body, ..} = do
  let fullType = maybeForall _convDefArgs <$> _convDefType
      allArgs = _convDefArgs <++ args
      (resultType, convArgs') = case fullType of
        Just ty | Right (ty', args', UTIBIsTypeTooShort False) <- useTypeInBinders ty allArgs ->
          (Just ty', args')
        _ -> (Nothing, allArgs)
  termination <- view (edits.termination.at _convDefName)
  struct <- case termination of
    Just (StructOrderTA (StructId_  n)) -> (pure . Just) (StructOrder n)
    Just (StructOrderTA (StructPos_ i)) ->
      case args ^? elementOf (traverse . binderNames) (i - 1) of
        Just (Ident name) -> (pure . Just) (StructOrder name)
        Just UnderscoreName ->
          throwProgramError ("error: function " ++ showP _convDefName ++ ": its " ++ show i ++ "-th argument is unnamed")
        Nothing -> throwProgramError ("error: function " ++ showP _convDefName ++ " has fewer than " ++ show i ++ " arguments")
    _ -> pure Nothing
  let b = RecDef
        { rdName       = _convDefName
        , rdArgs       = convArgs'
        , rdStruct     = struct
        , rdResultType = resultType
        , rdFullType   = fullType
        , rdBody       = body }
  pure (b, termination)
fixConvertedDefinition cd =
  convUnsupportedIn "recursion through non-lambda value" "definition" (showP $ cd^.convDefName)

splitArgs :: (ConversionMonad r m, Traversable t) => t ConvertedDefinition -> m ([Binder], t ConvertedDefinition)
splitArgs cds = do
  polyrec <- findM (\rd -> view $ edits.polyrecs.at (_convDefName rd)) cds
  case polyrec of
    Nothing -> pure (splitCommonPrefixOf convDefArgs cds)
    Just _  -> pure ([], cds)

--------------------------------------------------------------------------------

convertLocalBinds :: LocalConvMonad r m => HsLocalBinds GhcRn -> m Term -> m Term
#if __GLASGOW_HASKELL__ >= 806
#if __GLASGOW_HASKELL__ < 910
convertLocalBinds (XHsLocalBindsLR v) _ = noExtCon v
#endif
convertLocalBinds (HsValBinds _ ValBinds{}) _ =
  convUnsupported "Unexpected ValBinds in post-renamer AST"

convertLocalBinds (HsValBinds _ (XValBindsLR (NValBinds recBinds lsigs))) body = do
#else
convertLocalBinds (HsValBinds ValBindsIn{}) _ =
  convUnsupported "Unexpected ValBindsIn in post-renamer AST"

convertLocalBinds (HsValBinds (ValBindsOut recBinds lsigs)) body = do
#endif
  sigs     <- convertLSigs lsigs
  -- We are not actually using the rec_flag from GHC, because due to renamings
  -- or `redefinition` edits, maybe the group is no longer recursive.
  convDefss <- for recBinds $ \(_rec_flag, mut_group) ->
    convertTypedBindings (bagToList mut_group) sigs pure Nothing
  let convDefs = concat convDefss

  let fromConvertedBinding cb body = case cb of
        ConvertedDefinitionBinding ConvertedDefinition{..} ->
          pure (Let _convDefName _convDefArgs _convDefType _convDefBody body)
        ConvertedPatternBinding pat term -> do
          is_complete <- isCompleteMultiPattern [MultPattern [pat]]
          pure $ Coq.Match [MatchItem term Nothing Nothing] Nothing $
              Equation [MultPattern [pat]] body :
              [ Equation [MultPattern [UnderscorePat]] patternFailure | not is_complete ]
        ConvertedAxiomBinding ax _ty ->
          convUnsupported $ "local axiom `" ++ T.unpack (qualidToIdent ax) ++ "' unsupported"
        RedefinedBinding _nm _sn -> convUnsupported "redefining local bindings"
        SkippedBinding _nm -> convUnsupported "skipping local binding"
      
  (foldrM fromConvertedBinding ?? convDefs) =<< body

convertLocalBinds (HsIPBinds NOEXTP _) _ =
  convUnsupported "local implicit parameter bindings"
convertLocalBinds (EmptyLocalBinds NOEXTP) body =
  body

--------------------------------------------------------------------------------

-- Create `let x := rhs in genBody x`
-- Unless the rhs is very small, in which case it creates `genBody rhs`
bindIn :: LocalConvMonad r m => Text -> Term -> (Term -> m Term) -> m Term
bindIn _ rhs@(Qualid _) genBody = genBody rhs
bindIn tmpl rhs genBody = do
  j <- genqid tmpl
  body <- genBody (Qualid j)
  pure $ smartLet j rhs body


-- This prevents the pattern conversion code to create
-- `let j_24__ := … in j_24__`
-- and a few other common and obviously stupid forms
--
-- Originally, we avoided pushing the `rhs` past a binder. But it turned out
-- that we need to do that to get useful termination proof obligations out of
-- program fixpoint. So now we move the `rhs` past a binder if that binder is fresh (i.e. cannot be captured).
-- Let’s cross our fingers that we calculate all free variables properly.
smartLet :: Qualid -> Term -> Term -> Term
-- Move into the else branch
smartLet ident rhs (If is c Nothing t e)
    | ident `S.notMember` getFreeVars c
    , ident `S.notMember` getFreeVars t
    = If is c Nothing t (smartLet ident rhs e)
-- Move into the scrutinee
smartLet ident rhs
    (Coq.Match [MatchItem t Nothing Nothing] Nothing eqns)
    | ident `S.notMember` getFreeVars eqns
    = Coq.Match [MatchItem (smartLet ident rhs t) Nothing Nothing] Nothing eqns
-- Move into the last equation
-- (only if not mentioned in any earlier equation and only if no matched
-- variables is caught)
smartLet ident rhs
    (Coq.Match scruts Nothing eqns)
    | ident `S.notMember` getFreeVars (fmap NoBinding scruts)
    , let intoEqns [] = Just []
          intoEqns [Equation pats body] = do
            let bound = S.fromList $ foldMap definedBy pats
            guard $ ident `S.notMember` bound
            guard $ S.null $ bound `S.intersection` getFreeVars rhs
            return [Equation pats (smartLet ident rhs body)]
          intoEqns (e:es) = do
            guard $ ident `S.notMember` getFreeVars e
            (e:) <$> intoEqns es
    , Just eqns' <- intoEqns eqns
    = Coq.Match scruts Nothing eqns'
smartLet ident rhs (Qualid v) | ident == v = rhs
smartLet ident rhs body = Let ident [] Nothing rhs body

patternFailure :: Term
patternFailure = "GHC.Err.patternFailure"

missingValue :: Term
missingValue = "missingValue"

-- | Program does not work nicely with if-then-else, so if we believe we are
-- producing a term that ends up in a Program Fixpoint or Program Definition,
-- then desguar if-then-else using case statements.
ifThenElse :: LocalConvMonad r m => m (IfStyle -> Term -> Term -> Term -> Term)
ifThenElse = useProgramHere >>= \case
    False -> pure $ evalConstScrut IfBool
    True ->  pure $ evalConstScrut IfCase
  where
    -- Reduce `if true` and `if false`
    evalConstScrut :: (IfStyle -> Term -> Term -> Term -> Term)
                   -> (IfStyle -> Term -> Term -> Term -> Term)
    evalConstScrut _ _ "true"  e _ = e
    evalConstScrut _ _ "false" _ e = e
    evalConstScrut ifComb is scrut e1 e2 = ifComb is scrut e1 e2
