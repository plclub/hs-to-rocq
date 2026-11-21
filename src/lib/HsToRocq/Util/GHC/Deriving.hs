{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ < 900
{-# LANGUAGE TypeApplications #-}
#endif
#endif

#include "ghc-compat.h"

{- | Expose GHC's derived source bindings to the converter. The retained
declarations are typechecked by GHC first; re-deriving must agree with that
module's instance metadata, and must retain supporting bindings. -}

module HsToRocq.Util.GHC.Deriving (initForDeriving, addDerivedInstances
#if __GLASGOW_HASKELL__ >= 910
  , renameForDeriving, derivationIsSkipped, derivingRequests
  , removeDerivingRequest, failedDerivationType, sameDerivingSpan
  , neededDerivingBinds
#endif
  ) where

import GHC

import Control.Monad
import Data.Maybe (mapMaybe, listToMaybe, isJust)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

-- GHC version-gated imports: GHC 9.0+ reorganized internal modules under
-- GHC.* hierarchies; older versions use flat module names (e.g. TcRnMonad).
#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Parser.Annotation (noAnn)
#elif __GLASGOW_HASKELL__ >= 808
import GhcPlugins (SourceText(NoSourceText), PromotionFlag(NotPromoted))
#else
import GhcPlugins (SourceText(NoSourceText))
#endif

import GHC.IO (throwIO)
import qualified Control.Exception as E
#if __GLASGOW_HASKELL__ >= 902
import GHC.Utils.Outputable
import GHC.Driver.Session
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.TcType
import GHC.Tc.TyCl (tcTyAndClassDecls)
import GHC.Tc.TyCl.Instance (tcInstDeclsDeriv)
import GHC.Types.SourceFile (HscSource(HsSrcFile))
import GHC.Types.SourceText (SourceText(NoSourceText))
import GHC.Types.Var
import GHC.Types.Error
import GHC.Driver.Errors.Types (GhcMessage(GhcTcRnMessage))
import GHC.Core.Type as Type
import GHC.Core.TyCo.Rep
import GHC.Core.InstEnv (instanceSig, identicalClsInstHead, instEnvElts, is_dfun)
#else
import Outputable
import TcRnMonad
import TcEnv
import InstEnv
import Var
import TyCoRep
import TyCon
import Type
import TcType
import HscTypes
import TcInstDcls
#if __GLASGOW_HASKELL__ >= 810
import TcTyClsDecls
#endif
import Module
import SrcLoc
import FastString
import DynFlags
#endif
import qualified GHC.LanguageExtensions as LangExt

#if __GLASGOW_HASKELL__ >= 910
import qualified Control.Monad.Catch as MC
import GHC.Driver.Plugins
import GHC.Unit.Module.ModDetails (md_insts)
import Control.Lens hiding (Strict)
import HsToRocq.ConvertHaskell.Monad
import HsToRocq.ConvertHaskell.Variables (var)
import HsToRocq.ConvertHaskell.Declarations.Instances (convertInstanceNameAndTy)
import qualified HsToRocq.Edits.Types as Edits
import HsToRocq.Util.GHC.Module (ModuleData(..), mkModuleNameT)
import HsToRocq.Rocq.Gallina (Qualid(..))
import Data.Generics (everything, everythingBut, extQ, mkQ, everywhere, mkT)
import Data.Data (Data)
import GHC.Tc.Errors.Types (TcRnMessage(..), TcRnMessageDetailed(..), SolverReportWithCtxt(..), SolverReportErrCtxt(..), mkTcRnUnknownMessage)
import GHC.Tc.Types.Constraint (ic_info)
import GHC.Tc.Types.Origin (SkolemInfoAnon(DerivSkol), UserTypeCtxt(InstDeclCtxt))
import GHC.Core.Predicate (mkClassPred)
import GHC.Core.Unify (tcMatchTys, tcUnifyTy)
import GHC.Core.TyCo.Subst (substTys)
import GHC.Tc.Deriv (DerivInfo(..))
import GHC.Tc.Gen.HsType (tcHsClsInstType, tcHsDeriv, tcDerivStrategy)
import GHC.Builtin.Names (typeableClassName)

-- Use source dependencies and the converter's checked instance-name calculation,
-- including type and module renames. Diagnostics can omit the source context.
derivationIsSkipped :: GlobalMonad r m => ModuleName -> LHsType GhcRn -> LHsType GhcRn -> m Bool
derivationIsSkipped mod sourceTy headTy = uncurry (||) <$> derivationSkips mod sourceTy headTy

-- Only source syntax determines skipped dependencies. A checked head supplies
-- the canonical instance name, including inferred kinds and eta reduction.
-- Preserve the converter's skip-instance comment for a successful derivation,
-- while keeping dependency-skipped instances and unused helpers out of output.
derivationSkips :: GlobalMonad r m => ModuleName -> LHsType GhcRn -> LHsType GhcRn -> m (Bool, Bool)
derivationSkips mod sourceTy headTy = do
  targetMod <- view (edits.Edits.renamedModules.at mod.non mod)
  withCurrentModule (ModuleData targetMod [] mempty mempty mempty) $ do
    skipMods <- view (edits.Edits.skippedModules)
    skipCls <- view (edits.Edits.skippedClasses)
    moduleRenames <- view (edits.Edits.renamedModules)
    let names = collectNamesFromHsType (unLoc sourceTy)
        skippedModuleNames = skipMods `S.union` S.map (\m -> M.findWithDefault m m moduleRenames) skipMods
    qids <- traverse (var Edits.TypeNS) names
    let skippedName = any (`S.member` skipCls) qids
          || any (maybe False ((`S.member` skipMods) . moduleName) . nameModule_maybe) names
          || any (\case
                    Qualified m _ -> mkModuleNameT m `S.member` skippedModuleNames
                    _ -> False) qids
    if skippedName then pure (True, False) else
      -- Early kind errors can precede GHC's construction of the full inline
      -- instance head. A bare class still supports class/module skips, but
      -- cannot identify an individual instance. Preserve the GHC diagnostic.
      if hasArgument (unLoc headTy) then do
        (instName, _) <- convertInstanceNameAndTy (instanceHeadType headTy)
        instanceSkip <- view (edits.Edits.skipped.contains instName)
        pure (False, instanceSkip)
      else pure (False, False)
  where
    hasArgument (HsAppTy {}) = True
    hasArgument (HsOpTy {}) = True
    hasArgument (HsForAllTy _ _ body) = hasArgument (unLoc body)
    hasArgument (HsQualTy _ _ body) = hasArgument (unLoc body)
    hasArgument (HsParTy _ body) = hasArgument (unLoc body)
    hasArgument (HsKindSig _ body _) = hasArgument (unLoc body)
    hasArgument _ = False

instanceHeadType :: LHsType GhcRn -> LHsType GhcRn
instanceHeadType ty = case unLoc ty of
  HsForAllTy _ _ body -> instanceHeadType body
  HsQualTy _ _ body -> instanceHeadType body
  HsParTy _ body -> instanceHeadType body
  _ -> ty

data DerivingRequest = DerivingRequest
  { requestSpan :: SrcSpan
  , requestSyntax :: LHsType GhcRn
  , requestClass :: Class
  , requestTypes :: [Type]
  , requestIsInline :: Bool
  }

requestHead :: DerivingRequest -> Type
requestHead request = mkClassPred (requestClass request) (requestTypes request)

requestMatches :: DerivingRequest -> ClsInst -> Bool
requestMatches request spec =
  let (_, _, cls, tys) = instanceSig spec
  in getName (requestClass request) == getName cls
     && isJust (tcMatchTys (requestTypes request) tys)

requestMatchesExactly :: DerivingRequest -> ClsInst -> Bool
requestMatchesExactly request spec =
  let (_, _, _, tys) = instanceSig spec
  in requestMatches request spec && isJust (tcMatchTys tys (requestTypes request))

derivingClauseTypes :: HsDerivingClause (GhcPass pass) -> [LHsSigType (GhcPass pass)]
derivingClauseTypes clause = case unLoc (deriv_clause_tys clause) of
  DctSingle _ ty -> [ty]
  DctMulti _ tys -> tys

-- Inspect every declaration before generating bodies. These typed heads are
-- independent of InstInfo and md_insts, so losing both cannot pass validation.
checkedDerivingRequests :: [DerivInfo] -> [LDerivDecl GhcRn] -> TcM [DerivingRequest]
checkedDerivingRequests infos standalone = do
  standaloneRequests <- forM standalone $ \decl -> setSrcSpan (getLocA decl) $ do
    let deriv = unLoc decl
        L loc sig = hswc_body (deriv_type deriv)
        syntax = sig_body sig
        -- GHC also removes an extra-constraints wildcard before checking the
        -- head; its inferred context does not change which instance is wanted.
        checkedSig = case splitLHsQualTy syntax of
          (Just (L _ [pred]), body) | HsWildCardTy {} <- unLoc (ignoreParens pred) ->
            L loc sig { sig_body = body }
          _ -> L loc sig
    (_, viaTVs) <- tcDerivStrategy (deriv_strategy deriv)
    dfun <- tcExtendTyVarEnv viaTVs $ tcHsClsInstType (InstDeclCtxt True) checkedSig
    let (_, _, cls, tys) = tcSplitDFunTy dfun
    pure (DerivingRequest (getLocA decl) syntax cls tys False)
  inlineRequests <- fmap concat $ forM infos $ \info ->
    tcExtendNameTyVarEnv (di_scoped_tvs info) $ fmap concat $ forM (di_clauses info) $ \(L _ clause) -> do
      (_, viaTVs) <- tcDerivStrategy (deriv_clause_strategy clause)
      tcExtendTyVarEnv viaTVs $ forM (derivingClauseTypes clause) $ \ty -> setSrcSpan (getLocA ty) $ do
        (_, cls, clsArgs, argKinds) <- tcHsDeriv ty
        let rep = di_rep_tc info
            (tc, args) = case tyConFamInstSig_maybe rep of
              Just (family, patterns, _) -> (family, patterns)
              Nothing -> (rep, mkTyVarTys (tyConTyVars rep))
        case argKinds of
          [argKind] -> do
            let keep = length args - length (fst (splitFunTys argKind))
                applied = mkTyConApp tc (take keep args)
            case tcUnifyTy (Type.typeKind applied) argKind of
              Just sub | keep >= 0 ->
                pure (DerivingRequest (getLocA ty) (sig_body (unLoc ty)) cls
                        (substTys sub (clsArgs ++ [applied])) True)
              _ -> failWithTc $ mkTcRnUnknownMessage $ mkPlainDiagnostic ErrorWithoutFlag [] $
                     text "Cannot recover the checked inline deriving head" <+> ppr ty
          _ -> failWithTc (TcRnNonUnaryTypeclassConstraint ty)
  pure (standaloneRequests ++ inlineRequests)

parsedDerivingSpans :: ParsedModule -> [SrcSpan]
parsedDerivingSpans pm =
  [ getLocA decl | decl@(L _ (DerivD _ _)) <- hsmodDecls (unLoc (pm_parsed_source pm)) ]
  ++ everything (++) ([] `mkQ` inline) (pm_parsed_source pm)
  where
    inline :: HsDataDefn GhcPs -> [SrcSpan]
    inline defn = concatMap (map getLocA . derivingClauseTypes . unLoc) (dd_derivs defn)

sameRequestSpans :: [SrcSpan] -> [SrcSpan] -> Bool
sameRequestSpans [] b = null b
sameRequestSpans (a:as) b = case break (sameDerivingSpan a) b of
  (before, _:after) -> sameRequestSpans as (before ++ after)
  _ -> False

-- Stop at GHC's renamer boundary, before deriving or value typechecking can
-- fail. In particular, value declarations may need one of the wanted instances.
data RenamedForDeriving = RenamedForDeriving TcGblEnv (HsGroup GhcRn)
instance Show RenamedForDeriving where
  show _ = "RenamedForDeriving"
instance E.Exception RenamedForDeriving

renameForDeriving :: GhcMonad m => ParsedModule -> m (TcGblEnv, HsGroup GhcRn)
renameForDeriving pm = MC.bracket getSession setSession $ \env -> do
  let capture = defaultPlugin { renamedResultAction = \_ gbl group ->
        liftIO $ E.throwIO (RenamedForDeriving gbl group) }
      plugins = hsc_plugins env
  setSession env { hsc_plugins = plugins
    { staticPlugins = staticPlugins plugins ++ [StaticPlugin (PluginWithArgs capture [])] } }
  MC.catch (typecheckModule pm >> error "renameForDeriving: renamer hook did not run")
            (\(RenamedForDeriving gbl group) -> pure (gbl, group))
#endif

-- We need to allow IncoherentInstances for the hack in HsToRocq.Util.GHC.Deriving
initForDeriving :: GhcMonad m => m ()
initForDeriving =
  void $ getSessionDynFlags >>= setSessionDynFlags . (`xopt_set` LangExt.IncoherentInstances)

#if __GLASGOW_HASKELL__ >= 910
-- A kind annotation describes a type's kind, not another type/class used by
-- the instance. GHC adds these annotations when reconstructing derived heads;
-- treating their Type/RuntimeRep names as dependencies can skip valid requests.
collectNamesFromHsType :: HsType GhcRn -> [Name]
collectNamesFromHsType = everythingBut (++)
  ((([], False) `mkQ` (\(name :: Name) -> ([name], True))) `extQ` kinds)
  where
    kinds :: HsType GhcRn -> ([Name], Bool)
    kinds (HsKindSig _ body _) = (collectNamesFromHsType (unLoc body), True)
    kinds (HsAppKindTy _ body _) = (collectNamesFromHsType (unLoc body), True)
    kinds (HsForAllTy _ _ body) = (collectNamesFromHsType (unLoc body), True)
    kinds _ = ([], False)

-- GHC error spans omit buffer offsets, while syntax annotations retain them.
sameDerivingSpan :: SrcSpan -> SrcSpan -> Bool
sameDerivingSpan (RealSrcSpan a _) (RealSrcSpan b _) = a == b
sameDerivingSpan a b = a == b

derivingRequests :: HsGroup GhcRn -> [(SrcSpan, LHsType GhcRn)]
derivingRequests group =
  [ (getLocA d, sig_body (unLoc (hswc_body (deriv_type (unLoc d)))))
  | d <- hs_derivds group ]
  ++ everything (++) ([] `mkQ` inline) group
  where
    inline :: HsDataDefn GhcRn -> [(SrcSpan, LHsType GhcRn)]
    inline defn =
      [ (getLocA ty, sig_body (unLoc ty))
      | L _ clause <- dd_derivs defn, ty <- derivingClauseTypes clause ]

-- For inline requests, the diagnostic supplies the fully applied instance
-- head, including eta reduction for higher-kinded classes. Do not guess it
-- from the spelling of the class or the number of datatype parameters.
failedDerivationType :: GhcMessage -> Maybe (LHsType GhcRn)
failedDerivationType (GhcTcRnMessage msg) = go msg
  where
    go (TcRnMessageWithInfo _ (TcRnMessageDetailed _ inner)) = go inner
    go (TcRnWithHsDocContext _ inner) = go inner
    go (TcRnCannotDeriveInstance cls args _ _ _) = Just (typeToLHsType' (mkClassPred cls args))
    go (TcRnSolverReport report _) = listToMaybe
      [ typeToLHsType' ty
      | implication <- cec_encl (reportContext report)
      , DerivSkol ty <- [ic_info implication] ]
    go _ = Nothing
failedDerivationType _ = Nothing

removeDerivingRequest :: SrcSpan -> ParsedModule -> ParsedModule
removeDerivingRequest span pm =
  let L loc hsmod = pm_parsed_source pm
      keep (L declLoc (DerivD _ _)) = not (sameDerivingSpan span (locA declLoc))
      keep (L declLoc (InstD _ (ClsInstD _ _))) = not (sameDerivingSpan span (locA declLoc))
      keep _ = True
      withoutStandalone = hsmod { hsmodDecls = filter keep (hsmodDecls hsmod) }
      inline :: HsDataDefn GhcPs -> HsDataDefn GhcPs
      inline defn = defn { dd_derivs = mapMaybe clause (dd_derivs defn) }
      clause (L loc clause') =
        let L tysLoc tys = deriv_clause_tys clause'
            keepTy ty = not (sameDerivingSpan span (getLocA ty))
        in case tys of
          DctSingle _ ty | not (keepTy ty) -> Nothing
          DctMulti ext ts -> case filter keepTy ts of
            [] -> Nothing
            retained -> Just (L loc clause' { deriv_clause_tys = L tysLoc (DctMulti ext retained) })
          _ -> Just (L loc clause')
  in pm { pm_parsed_source = L loc (everywhere (mkT inline) withoutStandalone) }
#endif

-- | Re-derive checked declarations. There is deliberately no per-request
-- silent fallback: failures must pass through the caller's deriving policy.
-- Return auxiliary bindings separately: only conversion knows which original
-- method bodies survive the effective class interface and scoped edits.
#if __GLASGOW_HASKELL__ >= 910
addDerivedInstances :: GlobalMonad r m => TypecheckedModule -> m (TypecheckedModule, HsValBinds GhcRn)
#else
addDerivedInstances :: GhcMonad m => TypecheckedModule -> m (TypecheckedModule, HsValBinds GhcRn)
#endif
addDerivedInstances tcm = do
#if __GLASGOW_HASKELL__ >= 910
    (hsgroup, a, b, c, d) <- case tm_renamed_source tcm of
      Just x  -> pure x
      Nothing -> error "addDerivedInstances: TypecheckedModule has no renamed source"
#else
    (hsgroup, a, b, c) <- case tm_renamed_source tcm of
      Just x  -> pure x
      Nothing -> error "addDerivedInstances: TypecheckedModule has no renamed source"
#endif

#if __GLASGOW_HASKELL__ >= 910
    (inst_infos, aux_binds, requests) <- _initTcHack tcm $ do
#else
    (inst_infos, aux_binds) <- _initTcHack tcm $ do
#endif
        let tcg_env = fst (tm_internals_ tcm)
            tcg_env_hack = tcg_env { tcg_mod = fakeDerivingMod, tcg_semantic_mod = fakeDerivingMod }
                -- Set the module to make it look like we are in GHCi
                -- so that GHC will allow us to re-typecheck existing instances
        setGblEnv tcg_env_hack $
#if __GLASGOW_HASKELL__ >= 910
            do (gbl, _, deriv_infos, _) <- tcTyAndClassDecls (hs_tyclds hsgroup)
               setGblEnv gbl $ do
                 requests <- checkedDerivingRequests deriv_infos (hs_derivds hsgroup)
                 (_, infos, binds) <- tcInstDeclsDeriv deriv_infos (hs_derivds hsgroup)
                 failIfErrsM
                 return (infos, binds, requests)
#elif __GLASGOW_HASKELL__ >= 810
            do (gbl, _, deriv_info) <- tcTyAndClassDecls (hs_tyclds hsgroup)
               setGblEnv gbl $ do
                 (_, infos, binds) <- tcInstDeclsDeriv deriv_info (hs_derivds hsgroup)
                 failIfErrsM
                 return (infos, binds)
#else
            do (_, infos, binds) <- tcInstDeclsDeriv [] (hs_tyclds hsgroup >>= group_tyclds) (hs_derivds hsgroup)
               failIfErrsM
               return (infos, binds)
#endif

#if __GLASGOW_HASKELL__ >= 910
    let mod = ms_mod_name (pm_mod_summary (tm_parsed_module tcm))
        checked_insts = instEnvElts (md_insts (snd (tm_internals_ tcm)))
    let sourceSpans = map fst (derivingRequests hsgroup)
    unless (sameRequestSpans (parsedDerivingSpans (tm_parsed_module tcm)) sourceSpans
            && sameRequestSpans sourceSpans (map requestSpan requests)) $
      throwProgramError $ "Deriving requests changed between parsed, renamed, and checked source in "
        ++ moduleNameString mod ++ ":\n  parsed: "
        ++ showSDocUnsafe (ppr (parsedDerivingSpans (tm_parsed_module tcm)))
        ++ "\n  renamed: " ++ showSDocUnsafe (ppr sourceSpans)
        ++ "\n  checked: " ++ showSDocUnsafe (ppr (map requestSpan requests))
    policies <- forM (zip [0 :: Int ..] requests) $ \(index, request) -> do
      (dependencySkip, instanceSkip) <- derivationSkips mod (requestSyntax request) (typeToLHsType' (requestHead request))
      pure (index, request, dependencySkip, instanceSkip)
    associations <- forM inst_infos $ \info -> do
      let exact = [ policy | policy@(_, request, _, _) <- policies,
                             requestMatchesExactly request (iSpec info) ]
          -- Context inference may specialize an inline request's kinds
          -- (e.g. Generic1 (Compose f g) fixes f :: Type -> Type). Prefer
          -- exact matches, then allow these inline declaration templates.
          candidates = if null exact
            then [ policy | policy@(_, request, _, _) <- policies,
                            requestIsInline request, requestMatches request (iSpec info) ]
            else exact
      case candidates of
        [(index, _, dependencySkip, instanceSkip)] -> pure (info, index, dependencySkip, instanceSkip)
        _ -> throwProgramError $ "Derived instance must match exactly one source request: "
               ++ showSDocUnsafe (ppr (iSpec info))
    let retainedInfos = [ info | (info, _, False, _) <- associations ]
    forM_ inst_infos $ \info ->
      unless (any (identicalClsInstHead (iSpec info)) checked_insts) $
        throwProgramError $ showSDocUnsafe (ppr (getSrcSpan (is_dfun (iSpec info))))
          ++ ": derived instance has no matching checked metadata: " ++ showSDocUnsafe (ppr (iSpec info))
    -- Start from source requests, not dictionary locations or reconstructed
    -- signatures. Both metadata and the retained body must account for each
    -- wanted request, even if GHC's metadata has a different source span.
    -- Typeable deriving is a compiler-recognized no-op, not a local dictionary.
    forM_ policies $ \(index, request, dependencySkip, instanceSkip) ->
      unless (dependencySkip || instanceSkip || getName (requestClass request) == typeableClassName) $ do
        let bodies = [ info | (info, index', False, False) <- associations, index == index' ]
            metadataCount = case bodies of
              [info] -> length (filter (identicalClsInstHead (iSpec info)) checked_insts)
              _ -> length (filter (requestMatches request) checked_insts)
            bodyCount = length bodies
        unless (metadataCount == 1 && bodyCount == 1) $
          throwProgramError $ showSDocUnsafe (ppr (requestSpan request))
            ++ ": wanted deriving request must have exactly one checked dictionary and retained body: "
            ++ showSDocUnsafe (ppr (requestHead request))
            ++ " (metadata=" ++ show metadataCount ++ ", bodies=" ++ show bodyCount ++ ")"
    let inst_decls = map instInfoToDecl retainedInfos
#else
    let inst_decls = map instInfoToDecl inst_infos
#endif

#if __GLASGOW_HASKELL__ >= 806
    let mkTyClGroup decls instds = TyClGroup
          { group_ext = NOEXT
          , group_tyclds = decls
          , group_roles = []
#if __GLASGOW_HASKELL__ >= 810
          , group_kisigs = []
#endif
          , group_instds = instds
          }
#endif
    let hsgroup' = hsgroup { hs_tyclds = mkTyClGroup [] inst_decls : hs_tyclds hsgroup }

#if __GLASGOW_HASKELL__ >= 910
    return (tcm { tm_renamed_source = Just (hsgroup', a, b, c, d) }, aux_binds)
#else
    return (tcm { tm_renamed_source = Just (hsgroup', a, b, c) }, aux_binds)
#endif

_initTcHack :: GhcMonad m => TypecheckedModule -> TcM a -> m a
_initTcHack tcm action = do
 hsc_env <- getSession
 let hsc_env_tmp = hsc_env
        { hsc_dflags = ms_hspp_opts (pm_mod_summary (tm_parsed_module tcm)) }
 let mod = fakeDerivingMod
 -- let mod = icInteractiveModule (hsc_IC hsc_env)
 let src_span = realSrcLocSpan (mkRealSrcLoc (fsLit "<deriving>") 1 1)

 (msgs, mba) <- liftIO $ initTc hsc_env_tmp HsSrcFile False mod src_span action
 case mba of Just x ->  return x
             Nothing -> liftIO $ throwIO $ mkSrcErr $
#if __GLASGOW_HASKELL__ >= 900
               fmap GhcTcRnMessage msgs
#else
               snd msgs
#endif

#if __GLASGOW_HASKELL__ >= 910
-- Keep complete binding groups reachable from translated instance bodies. GHC
-- can return shared helpers separately (e.g. tag-to-constructor functions for Enum).
-- Names bound inside a body may conservatively retain a helper, but a helper
-- needed by a body or by another helper must never be lost.
neededDerivingBinds :: [HsBind GhcRn] -> HsValBinds GhcRn -> HsValBinds GhcRn
neededDerivingBinds methods (XValBindsLR (NValBinds groups sigs)) =
  let names :: Data a => a -> S.Set Name
      names = everything S.union (S.empty `mkQ` S.singleton)
      bound = S.fromList . collectHsBindsBinders CollNoDictBinders . snd
      close used =
        let used' = used `S.union` S.unions
              [ names binds | group@(_, binds) <- groups, not (S.disjoint used (bound group)) ]
        in if used' == used then used else close used'
      used = close (names methods)
  in XValBindsLR (NValBinds
       (filter (not . S.disjoint used . bound) groups)
       (filter (not . S.disjoint used . names) sigs))
neededDerivingBinds _ binds = pprPanic "neededDerivingBinds: unrenamed bindings" (ppr binds)
#endif

fakeDerivingMod :: Module
fakeDerivingMod = mkModule
#if __GLASGOW_HASKELL__ >= 900
  interactiveUnit
#else
  interactiveUnitId
#endif
  (mkModuleName "Deriving")


-- | Convert a derived 'InstInfo' back into a source-level 'LInstDecl'.
-- GHC 9.0+ changed type signature representation: 'HsIB' was replaced by
-- 'HsSig' with 'HsOuterImplicit' for implicit type variable binding.
instInfoToDecl :: InstInfo GhcRn -> LInstDecl GhcRn
instInfoToDecl inst_info =
#if __GLASGOW_HASKELL__ >= 900
  noLocA
#else
  noLoc
#endif
    $ ClsInstD NOEXT (ClsInstDecl
    { cid_binds = ib_binds (iBinds inst_info)
    , cid_sigs = []
    , cid_tyfam_insts = []
    , cid_datafam_insts = []
    , cid_overlap_mode = Nothing
#if __GLASGOW_HASKELL__ >= 900
    , cid_poly_ty = noLocA $ HsSig NOEXT (HsOuterImplicit tvars_) $ noLocA $ HsQualTy NOEXT (noLocA ctxt) inst_head
#elif __GLASGOW_HASKELL__ >= 808
    , cid_poly_ty = HsIB @GhcRn tvars_ (noLoc (HsQualTy NOEXT (noLoc ctxt) inst_head))
#elif __GLASGOW_HASKELL__ == 806
    , cid_poly_ty = HsIB @GhcRn (HsIBRn tvars_ True) (noLoc (HsQualTy NOEXT (noLoc ctxt) inst_head))
#else
    , cid_poly_ty = HsIB tvars_ (noLoc (HsQualTy (noLoc ctxt) inst_head)) True
#endif
#if __GLASGOW_HASKELL__ >= 910
    , cid_ext = Nothing
#elif __GLASGOW_HASKELL__ >= 806
    , cid_ext = NOEXT
#endif
    })
  where
    (tvars, theta, cls, args) = instanceSig (iSpec inst_info)
    tvars_ :: [Name]
    tvars_ = map tyVarName tvars
    ctxt = map typeToLHsType' theta
    inst_head = foldl lHsAppTy (noLocA (HsTyVar noAnn NotPromoted (noLocA (getName cls)))) $
        map typeToLHsType' args

    lHsAppTy f x = noLocA (HsAppTy NOEXT f x)

#if __GLASGOW_HASKELL__ >= 900
#define noLoc noLocA
#endif

-- Taken from HsUtils. We need it to produce a Name, not a RdrName.
-- GHC 9.0+ changes: 'splitFunTy' returns a 3-tuple (multiplicity, arg, res)
-- for linear types support; 'ForAllTy' uses 'HsForAllInvis'/'hst_tele'
-- instead of 'hst_bndrs'/'hst_fvf'; 'go_tv' gains a 'Specificity' parameter.
typeToLHsType' :: Type -> LHsType GhcRn
typeToLHsType' ty
  = go ty
  where
    go :: Type -> LHsType GhcRn
    go ty@(FunTy {})
#if __GLASGOW_HASKELL__ >= 900
      | (_, arg, res) <- splitFunTy ty =
#else
      | (arg, res) <- splitFunTy ty =
#endif
      if isPredTy arg then
        let (theta, tau) = tcSplitPhiTy ty in
        noLoc (HsQualTy { hst_ctxt = noLoc (map go theta)
                        , hst_body = go tau
#if __GLASGOW_HASKELL__ >= 806
                        , hst_xqual = NOEXT
#endif
                        })
      else nlHsFunTy (go arg) (go res)
    go ty@(ForAllTy {})
#if __GLASGOW_HASKELL__ >= 900
      | (tvs, tau) <- tcSplitForAllTyVars ty
#else
      | (tvs, tau) <- tcSplitForAllTys ty
#endif
      = noLoc (HsForAllTy {
#if __GLASGOW_HASKELL__ >= 900
                            hst_tele = HsForAllInvis noAnn (map go_tv tvs)
#else
                            hst_bndrs = map go_tv tvs
#if __GLASGOW_HASKELL__ >= 810
                          , hst_fvf = ForallInvis
#endif
#endif
                          , hst_body = go tau
#if __GLASGOW_HASKELL__ >= 806
                          , hst_xforall = NOEXT
#endif
                          })
#if __GLASGOW_HASKELL__ >= 900
    go (TyVarTy tv)         = nlHsTyVar NotPromoted (getName tv)
#else
    go (TyVarTy tv)         = nlHsTyVar (getName tv)
#endif
    go (AppTy t1 t2)        = nlHsAppTy (go t1) (go t2)
    go (LitTy (NumTyLit n))  = noLoc $ HsTyLit NOEXT (HsNumTy NoSourceText n)
    go (LitTy (StrTyLit s))  = noLoc $ HsTyLit NOEXT (HsStrTy NoSourceText s)
    go (LitTy (CharTyLit c)) = noLoc $ HsTyLit NOEXT (HsCharTy NoSourceText c)
    go ty@(TyConApp tc args)
      | any isInvisibleTyConBinder (tyConBinders tc)
        -- We must produce an explicit kind signature here to make certain
        -- programs kind-check. See Note [Kind signatures in typeToLHsType].
#if __GLASGOW_HASKELL__ >= 900
      = noLocA $ HsKindSig noAnn lhs_ty (go (Type.typeKind ty))
#else
      = noLoc $ HsKindSig NOEXT lhs_ty (go (Type.typeKind ty))
#endif
      | otherwise = lhs_ty
       where
        lhs_ty = nlHsTyConApp
#if __GLASGOW_HASKELL__ >= 900
#if __GLASGOW_HASKELL__ >= 910
          NotPromoted Prefix (getName tc) (map (HsValArg noExtField . go) args')
#else
          NotPromoted Prefix (getName tc) (map (HsValArg . go) args')
#endif
#else
          (getName tc) (map go args')
#endif
        args'  = filterOutInvisibleTypes tc args
    go (CastTy ty _)        = go ty
    go (CoercionTy co)      = pprPanic "toLHsSigWcType" (ppr co)

         -- Source-language types have _invisible_ kind arguments,
         -- so we must remove them here (Trac #8563)

    go_tv :: TyVar -> LHsTyVarBndr
#if __GLASGOW_HASKELL__ >= 900
      Specificity
#endif
      GhcRn
    go_tv tv = noLoc $ KindedTyVar
#if __GLASGOW_HASKELL__ >= 900
        noAnn InferredSpec
#else
        NOEXT
#endif
        (noLoc (getName tv)) (go (tyVarKind tv))
