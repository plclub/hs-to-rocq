{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TemplateHaskell            #-}

module HsToRocq.Edits.Types (
  Edits(..), typeSynonymTypes, dataTypeArguments, termination, redefinitions, additions, skipped, skippedConstructors, skippedClasses, skippedMethods, skippedEquations, skippedCasePatterns, skippedModules, importedModules, hasManualNotation, axiomatizedModules, axiomatizedOriginalModuleNames, axiomatizedDefinitions, unaxiomatizedDefinitions, additionalScopes, orders, renamings, coinductiveTypes, classKinds, dataKinds, polyKinds, deleteUnusedTypeVariables, rewrites, obligations, renamedModules, simpleClasses, inlinedMutuals, replacedTypes, collapsedLets, inEdits, exceptInEdits, promotions, polyrecs, universePolymorphic, universeCumulative, lookupUniverseStatus, equations, invariants,
  HsNamespace(..), NamespacedIdent(..), Renamings,
  DataTypeArguments(..), dtParameters, dtIndices,
  RocqDefinition(..), definitionSentence,
  anAssertionVariety,
  ScopePlace(..),
  StructOrder_(..), WFOrder_(..), fromOrder, fromWFOrder,
  TerminationArgument(..),
  NormalizedPattern(), getNormalizedPattern, normalizePattern,
  Rewrite(..), Rewrites,
  Edit(..), addEdit, buildEdits, subtractEdits, addInvariantEdit,
  useProgram,
  Phase(..),
) where

import           Prelude                           hiding (tail)

import           Control.Lens

import           HsToRocq.Util.Generics

import           Control.Monad
import           Control.Monad.Except
import           Data.List.NonEmpty                (NonEmpty (..), tail, toList, fromList)
import           Data.Semigroup
import qualified Data.Text                         as T
import           Data.Tuple

import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as M
import           Data.Set                          (Set)
import qualified Data.Set                          as S
import           Data.List                         ((\\))

import           HsToRocq.Util.GHC.Module

import           HsToRocq.Rocq.FreeVars              ()
import           HsToRocq.Util.FVs

import           HsToRocq.ConvertHaskell.Axiomatize
import           HsToRocq.Rocq.Gallina
import           HsToRocq.Rocq.Gallina.Rewrite       (Rewrite (..), Rewrites)
import           HsToRocq.Rocq.Gallina.Util
import           HsToRocq.Rocq.Pretty
import           HsToRocq.Rocq.Subst                 (Subst ())

--------------------------------------------------------------------------------

data DataTypeArguments = DataTypeArguments { _dtParameters :: ![Qualid]
                                           , _dtIndices    :: ![Qualid] }
                       deriving (Eq, Ord, Show, Read)
makeLenses ''DataTypeArguments

data RocqDefinition = RocqDefinitionDef Definition
                   | RocqFixpointDef   Fixpoint
                   | RocqInductiveDef  Inductive
                   | RocqInstanceDef   InstanceDefinition
                   | RocqAxiomDef      (Qualid, Term) -- Curry?  Uncurry?  A new type?
                   | RocqAssertionDef  (Assertion, Proof) -- Curry?  Uncurry?  A new type?
                   deriving (Eq, Ord, Show, Read)

definitionSentence :: RocqDefinition -> Sentence
definitionSentence (RocqDefinitionDef      def) = DefinitionSentence        def
definitionSentence (RocqFixpointDef        fix) = FixpointSentence          fix
definitionSentence (RocqInductiveDef       ind) = InductiveSentence         ind
definitionSentence (RocqInstanceDef        ind) = InstanceSentence          ind
definitionSentence (RocqAxiomDef           axm) = uncurry typedAxiom        axm
definitionSentence (RocqAssertionDef       apf) = uncurry AssertionSentence apf

anAssertionVariety :: (Assertion, Proof) -> String
anAssertionVariety (Assertion kwd _ _ _, _) = case kwd of
  Theorem     -> "a Theorem"
  Lemma       -> "a Lemma"
  Remark      -> "a Remark"
  Fact        -> "a Fact"
  Corollary   -> "a Corollary"
  Proposition -> "a Proposition"
  Definition  -> "a Definition"
  Example     -> "an Example"

instance HasBV Qualid RocqDefinition where
  bvOf = bvOf . definitionSentence

-- Add more as needed
data ScopePlace = SPValue | SPConstructor
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

data StructOrder_
  = StructId_ Qualid  -- ^ Name of decreasing argument
  | StructPos_ Int    -- ^ Position of decreasing argument, count from 1 (in Haskell, so excluding type arguments)
  deriving (Eq, Ord, Show, Read)

data WFOrder_
  = MeasureOrder_ Term (Maybe Term)  -- ^@measure /term/ (/term/)?/
  | WFOrder_ Term Qualid             -- ^@wf /term/ /ident//
  deriving (Eq, Ord, Show, Read)

fromWFOrder :: WFOrder_ -> Order
fromWFOrder (MeasureOrder_ t u) = MeasureOrder t u
fromWFOrder (WFOrder_ t u) = WFOrder t u

fromOrder :: Order -> TerminationArgument
fromOrder (StructOrder q) = StructOrderTA (StructId_ q)
fromOrder (MeasureOrder t u) = WellFoundedTA (MeasureOrder_ t u)
fromOrder (WFOrder t u) = WellFoundedTA (WFOrder_ t u)

-- | 'StructOrderTA' and 'WellFoundedTA' correspond to 'Coq.Order', but
-- we explicitily separate the 'StructOrder' case because it is used at a different
-- place in the translation, and we also recognize a special syntax for unnamed arguments.
data TerminationArgument
  = StructOrderTA StructOrder_
  | WellFoundedTA WFOrder_
  | Deferred
  | Corecursive
  deriving (Eq, Ord, Show, Read)

-- Used to match patterns that might disagree on the question of whether a name
-- is an @ArgsPat qid []@ or a @QualidPat@; this is useful when reading from an edits file.
newtype NormalizedPattern = NormalizedPattern Pattern
                          deriving (Eq, Ord, Show, Read, Subst, HasBV Qualid, Gallina)

getNormalizedPattern :: NormalizedPattern -> Pattern
getNormalizedPattern (NormalizedPattern pat) = pat
{-# INLINE getNormalizedPattern #-}

normalizePattern :: Pattern -> NormalizedPattern
normalizePattern = NormalizedPattern . go where
  go (ArgsPat         qid [])     = QualidPat       qid
  go (ArgsPat         qid args)   = ArgsPat         qid (go <$> args)
  go (ExplicitArgsPat qid args)   = ExplicitArgsPat qid (go <$> args)
  go (InfixPat        lhs op rhs) = InfixPat        (go lhs) op (go rhs)
  go (AsPat           p qid)      = AsPat           (go p) qid
  go (InScopePat      p scope)    = InScopePat      (go p) scope
  go (QualidPat       qid)        = QualidPat       qid
  go UnderscorePat                = UnderscorePat
  go (NumPat          n)          = NumPat          n
  go (StringPat       s)          = StringPat       s
  go (OrPats          ps)         = OrPats          (goO <$> ps)

  goO (OrPattern ps) = OrPattern (go <$> ps)

data Phase = PhaseTyCl | PhaseTerm deriving (Eq, Ord, Show)
type Additions = ([Sentence],[Sentence])
addPhase :: Phase -> Sentence -> Additions -> Additions
addPhase PhaseTyCl s (tcls,tms) = (s:tcls, tms)
addPhase PhaseTerm s (tcls,tms) = (tcls, s:tms)

data Edit = TypeSynonymTypeEdit              Ident Ident
          | DataTypeArgumentsEdit            Qualid DataTypeArguments
          | TerminationEdit                  Qualid TerminationArgument
          | ObligationsEdit                  Qualid Tactics
          | RedefinitionEdit                 RocqDefinition
          | AddEdit                          ModuleName RocqDefinition Phase
          | SkipEdit                         Qualid
          | SkipConstructorEdit              Qualid
          | SkipClassEdit                    Qualid
          | SkipMethodEdit                   Qualid Ident
          | SkipEquationEdit                 Qualid (NonEmpty Pattern)
          | SkipCasePatternEdit              Pattern
          | SkipModuleEdit                   ModuleName
          | ImportModuleEdit                 ModuleName
          | AxiomatizeModuleEdit             ModuleName
          | AxiomatizeOriginalModuleNameEdit ModuleName
          | AxiomatizeDefinitionEdit         Qualid
          | UnaxiomatizeDefinitionEdit       Qualid
          | HasManualNotationEdit            ModuleName
          | AdditionalScopeEdit              ScopePlace Qualid Ident
          | OrderEdit                        (NonEmpty Qualid)
          | RenameEdit                       NamespacedIdent Qualid
          | ClassKindEdit                    Qualid (NonEmpty Term)
          | DataKindEdit                     Qualid (NonEmpty Term)
          | PolyKindEdit                     Qualid (NonEmpty Ident)
          | DeleteUnusedTypeVariablesEdit    Qualid
          | RewriteEdit                      Rewrite
          | CoinductiveEdit                  Qualid
          | RenameModuleEdit                 ModuleName ModuleName
          | AliasModuleEdit                  ModuleIdent ModuleIdent  -- Resolved during parsing
          | SimpleClassEdit                  Qualid
          | InlineMutualEdit                 Qualid
          | SetTypeEdit                      Qualid (Maybe Term)
          | CollapseLetEdit                  Qualid
          | InEdit                           Qualid Edit
          | ExceptInEdit                     (NonEmpty Qualid) Edit
          | PromoteEdit                      Qualid
          | PolyrecEdit                      Qualid
          | UniversePolymorphicEdit          Qualid
          | UniverseCumulativeEdit           Qualid
          | EquationsEdit                    Qualid
          | InvariantEdit                    ModuleName Qualid [Binder] Ident [Qualid] RocqDefinition
          deriving (Eq, Ord, Show)

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

prettyNSIdent :: NamespacedIdent -> String
prettyNSIdent NamespacedIdent{..} = prettyNS niNS ++ " " ++ T.unpack (qualidToIdent niId) where
  prettyNS ExprNS = "value"
  prettyNS TypeNS = "type"

data NamespacedIdent = NamespacedIdent { niNS :: !HsNamespace
                                       , niId :: !Qualid }
                     deriving (Eq, Ord, Show, Read)

type Renamings = Map NamespacedIdent Qualid

{-
 Currently, addInvariant works by adding smaller edits.
 It does this by modifying the fields of the Edits
 structure that is passed along for later usage.

However, some information isn't available at the time addInvariant is called,
for example, the list of the module's exports.

So instead of creating the smaller edits within addInvariant, we have to pass
relevant information on so that those edits can be done when we do have
the needed information
 
-}
data InvEditInfo = InvEditInfo { 

                               } deriving (Eq, Ord, Show, Generic)

data Edits = Edits { _typeSynonymTypes               :: !(Map Ident Ident)
                   , _dataTypeArguments              :: !(Map Qualid DataTypeArguments)
                   , _termination                    :: !(Map Qualid TerminationArgument)
                   , _redefinitions                  :: !(Map Qualid RocqDefinition)
                   , _additions                      :: !(Map ModuleName Additions)
                   , _skipped                        :: !(Set Qualid)
                   , _skippedConstructors            :: !(Set Qualid)
                   , _skippedClasses                 :: !(Set Qualid)
                   , _skippedMethods                 :: !(Set (Qualid,Ident))
                   , _skippedEquations               :: !(Map Qualid (Set (NonEmpty NormalizedPattern)))
                   , _skippedCasePatterns            :: !(Set NormalizedPattern)
                   , _skippedModules                 :: !(Set ModuleName)
                   , _importedModules                :: !(Set ModuleName)
                   , _axiomatizedModules             :: !(Set ModuleName)
                   , _axiomatizedOriginalModuleNames :: !(Set ModuleName)
                   , _axiomatizedDefinitions         :: !(Set Qualid)
                   , _unaxiomatizedDefinitions       :: !(Set Qualid)
                   , _hasManualNotation              :: !(Set ModuleName)
                   , _additionalScopes               :: !(Map (ScopePlace, Qualid) Ident)
                   , _orders                         :: !(Map Qualid (Set Qualid))
                   , _classKinds                     :: !(Map Qualid (NonEmpty Term))
                   , _dataKinds                      :: !(Map Qualid (NonEmpty Term))
                   , _polyKinds                      :: !(Map Qualid (NonEmpty Ident))
                   , _deleteUnusedTypeVariables      :: !(Set Qualid)
                   , _renamings                      :: !Renamings
                   , _rewrites                       :: ![Rewrite]
                   , _obligations                    :: !(Map Qualid Tactics)
                   , _coinductiveTypes               :: !(Set Qualid)
                   , _renamedModules                 :: !(Map ModuleName ModuleName)
                   , _simpleClasses                  :: !(Set Qualid)
                   , _inlinedMutuals                 :: !(Set Qualid)
                   , _replacedTypes                  :: !(Map Qualid (Maybe Term)) -- Instead of setTypes
                   , _collapsedLets                  :: !(Set Qualid)
                   , _inEdits                        :: !(Map Qualid Edits)
                   , _exceptInEdits                  :: !(Map Qualid Edits)
                   , _promotions                     :: !(Set Qualid)
                   , _polyrecs                       :: !(Set Qualid)
                   , _universePolymorphic            :: !(Set Qualid)
                   , _universeCumulative             :: !(Set Qualid)
                   , _equations                      :: !(Set Qualid)
                   , _invariants                     :: !(Map Qualid InvEditInfo)

                   }
           deriving (Eq, Ord, Show, Generic)
instance Semigroup Edits where (<>)   = (%<>)
instance Monoid    Edits where mempty = gmempty
makeLenses ''Edits

{-
   Given two Edits structures, compute their "difference".
   The difference is computed component-wise.
   This is used for ExceptIn edits -- applying an edit everywhere except in
   one or more specified definitions.
   Note that for most kinds of edits, it doesn't make sense to use ExceptIn.
   For these edits, subtractEdits simply returns the corresponding component of
   the first argument.
-}
subtractEdits :: Edits -> Edits -> Edits
subtractEdits edits1 edits2 =
  Edits {
    _typeSynonymTypes               = edits1^.typeSynonymTypes
  , _dataTypeArguments              = edits1^.dataTypeArguments 
  , _termination                    = (edits1^.termination) M.\\ (edits2^.termination)
  , _redefinitions                  = edits1^.redefinitions
  , _additions                      = edits1^.additions
  , _skipped                        = edits1^.skipped
  , _skippedConstructors            = edits1^.skippedConstructors
  , _skippedClasses                 = edits1^.skippedClasses
  , _skippedMethods                 = edits1^.skippedMethods
  , _skippedEquations               = edits1^.skippedEquations
  , _skippedCasePatterns            = (edits1^.skippedCasePatterns) S.\\ (edits2^.skippedCasePatterns)
  , _skippedModules                 = edits1^.skippedModules
  , _importedModules                = edits1^.importedModules
  , _axiomatizedModules             = edits1^.axiomatizedModules
  , _axiomatizedOriginalModuleNames = edits1^.axiomatizedOriginalModuleNames
  , _axiomatizedDefinitions         = edits1^.axiomatizedDefinitions
  , _unaxiomatizedDefinitions       = edits1^.unaxiomatizedDefinitions
  , _hasManualNotation              = edits1^.hasManualNotation        -- ?
  , _additionalScopes               = edits1^.additionalScopes         -- ?
  , _orders                         = edits1^.orders
  , _classKinds                     = edits1^.classKinds
  , _dataKinds                      = edits1^.dataKinds
  , _polyKinds                      = edits1^.polyKinds
  , _deleteUnusedTypeVariables      = edits1^.deleteUnusedTypeVariables -- ?
  , _renamings                      = (edits1^.renamings) M.\\ (edits2^.renamings)
  , _rewrites                       = (edits1^.rewrites) \\ (edits2^.rewrites)
  , _obligations                    = edits1^.obligations
  , _coinductiveTypes               = edits1^.coinductiveTypes
  , _renamedModules                 = edits1^.renamedModules
  , _simpleClasses                  = edits1^.simpleClasses
  , _inlinedMutuals                 = edits1^.inlinedMutuals
  , _replacedTypes                  = edits1^.replacedTypes
  , _collapsedLets                  = edits1^.collapsedLets
  , _inEdits                        = edits1^.inEdits
  , _exceptInEdits                  = edits1^.exceptInEdits
  , _promotions                     = edits1^.promotions
  , _polyrecs                       = (edits1^.polyrecs) S.\\ (edits2^.polyrecs)
  , _universePolymorphic            = edits1^.universePolymorphic
  , _universeCumulative             = edits1^.universeCumulative
  , _equations                      = (edits1^.equations) S.\\ (edits2^.equations)
  , _invariants                     = edits1^.invariants
  }

-- Derived edits
useProgram :: Qualid -> Edits -> Bool
useProgram name edits =
    any isWellFounded (M.lookup name (_termination edits))
    || any (any isWellFounded . _termination) (M.lookup name (_inEdits edits))
    || name `M.member` _obligations edits
  where
   isWellFounded WellFoundedTA {} = True
   isWellFounded _                = False

-- | Look up the universe polymorphism/cumulativity status for a type name.
-- Cumulative subsumes polymorphic when both edits are present.
lookupUniverseStatus :: Qualid -> Edits -> UniverseStatus
lookupUniverseStatus name edits
  | name `S.member` _universeCumulative edits = UnivPolyCumulative
  | name `S.member` _universePolymorphic edits = UnivPoly
  | otherwise = NotUnivPoly

-- Module-local'
duplicateFor' :: String -> (a -> String) -> a -> String
duplicateFor' what disp x = "Duplicate " ++ what ++ " for " ++ disp x

-- Module-local
duplicateFor :: String -> String -> String
duplicateFor what = duplicateFor' what id

-- Module-local
duplicateIFor :: String -> Ident -> String
duplicateIFor what = duplicateFor' what T.unpack

-- Module-local
duplicateQFor :: String -> Qualid -> String
duplicateQFor what = duplicateFor' what (T.unpack . qualidToIdent)

-- Module-local
duplicatePFor :: Gallina g => String -> g -> String
duplicatePFor what = duplicateFor' what showP

descDuplEdit :: Edit                    -> String
descDuplEdit = \case
  TypeSynonymTypeEdit              syn        _ -> duplicateIFor  "type synonym result types"                      syn
  DataTypeArgumentsEdit            ty         _ -> duplicateQFor  "data type argument specifications"              ty
  TerminationEdit                  what _       -> duplicateQFor  "termination requests"                           what
  RedefinitionEdit                 def          -> duplicateQFor  "redefinitions"                                  (defName def)
  SkipEdit                         what         -> duplicateQFor  "skips"                                          what
  SkipConstructorEdit              con          -> duplicateQFor  "skipped constructor requests"                   con
  SkipClassEdit                    cls          -> duplicateQFor  "skipped class requests"                         cls
  SkipMethodEdit                   cls meth     -> duplicateFor   "skipped method requests"                        (prettyLocalName cls meth)
  SkipEquationEdit                 fun pats     -> duplicatePFor  "skipped equation requests"                      (ArgsPat fun $ toList pats)
  SkipCasePatternEdit              pat          -> duplicatePFor  "skipped case pattern requests"                  pat
  SkipModuleEdit                   mod          -> duplicateFor   "skipped module requests"                        (moduleNameString mod)
  ImportModuleEdit                 mod          -> duplicateFor   "imported module requests"                       (moduleNameString mod)
  HasManualNotationEdit            what         -> duplicateFor   "has manual notation"                            (moduleNameString what)
  AxiomatizeModuleEdit             mod          -> duplicateFor   "module axiomatizations"                         (moduleNameString mod)
  AxiomatizeOriginalModuleNameEdit mod          -> duplicateFor   "module axiomatizations under the original name" (moduleNameString mod)
  AxiomatizeDefinitionEdit         what         -> duplicateQFor  "definition axiomatizations"                     what
  UnaxiomatizeDefinitionEdit       what         -> duplicateQFor  "definition unaxiomatizations"                   what
  AdditionalScopeEdit              place name _ -> duplicateFor   "additions of a scope"                           (prettyScoped place name)
  RenameEdit                       hs _         -> duplicateFor   "renamings"                                      (prettyNSIdent hs)
  ClassKindEdit                    cls _        -> duplicateQFor  "class kinds"                                    cls
  DataKindEdit                     dat _        -> duplicateQFor  "data kinds"                                     dat
  PolyKindEdit                     dat _        -> duplicateQFor  "polykinds"                                      dat
  DeleteUnusedTypeVariablesEdit    qid          -> duplicateQFor  "unused type variables deletions"                qid
  ObligationsEdit                  what _       -> duplicateQFor  "obligation kinds"                               what
  CoinductiveEdit                  ty           -> duplicateQFor  "coinductive data types"                         ty
  RenameModuleEdit                 m1 _         -> duplicateFor   "renamed modules"                                (moduleNameString m1)
  AliasModuleEdit                  _ _          -> error "Alias module edits are never duplicates"
  AddEdit{}                                     -> error "Add edits are never duplicates"
  RewriteEdit                      _            -> error "Rewrites are never duplicates"
  OrderEdit                        _            -> error "Order edits are never duplicates"
  SimpleClassEdit                  cls          -> duplicateQFor  "simple class requests"                          cls
  InlineMutualEdit                 fun          -> duplicateQFor  "inlined mutually recursive functions"           fun
  SetTypeEdit                      qid _        -> duplicateQFor  "set types"                                      qid
  CollapseLetEdit                  qid          -> duplicateQFor  "collapsed lets"                                 qid
  InEdit                           _ _          -> error "In Edits are never duplicates"
  ExceptInEdit                     _ _          -> error "ExceptIn Edits are never duplicates"
  PromoteEdit                      qid          -> duplicateQFor  "promotions"                                     qid
  PolyrecEdit                      qid          -> duplicateQFor  "polymorphic recursion requests"                 qid
  UniversePolymorphicEdit          qid          -> duplicateQFor  "universe polymorphic requests"                  qid
  UniverseCumulativeEdit           qid          -> duplicateQFor  "universe cumulative requests"                   qid
  EquationsEdit                    qid          -> duplicateQFor  "equations requests"                              qid
  InvariantEdit                    _ qid _ _ _ _  -> duplicateQFor "Duplicate invariant for the same definition"   qid
  where
    prettyScoped place name = let pplace = case place of
                                    SPValue       -> "value"
                                    SPConstructor -> "constructor"
                              in pplace ++ ' ' : T.unpack (qualidToIdent name)

    prettyLocalName outer inner = T.unpack $ qualidToIdent outer <> "." <> inner

addEdit :: MonadError String m => Edit -> Edits -> m Edits
addEdit e = case e of
  TypeSynonymTypeEdit              syn  res         -> addFresh e typeSynonymTypes                       syn                         res
  DataTypeArgumentsEdit            ty   args        -> addFresh e dataTypeArguments                      ty                          args
  TerminationEdit                  what ta          -> addFresh e termination                            what                        ta
  RedefinitionEdit                 def              -> addFresh e redefinitions                          (defName def)               def
  SkipEdit                         what             -> addFresh e skipped                                what                        ()
  SkipConstructorEdit              con              -> addFresh e skippedConstructors                    con                         ()
  SkipClassEdit                    cls              -> addFresh e skippedClasses                         cls                         ()
  SkipMethodEdit                   cls meth         -> addFresh e skippedMethods                         (cls,meth)                  ()
  SkipEquationEdit                 fun pats         -> addFresh e (skippedEquations.at fun.non mempty)   (normalizePattern <$> pats) ()
  SkipCasePatternEdit              pat              -> addFresh e skippedCasePatterns                    (normalizePattern pat)      ()
  SkipModuleEdit                   mod              -> addFresh e skippedModules                         mod                         ()
  ImportModuleEdit                 mod              -> addFresh e importedModules                        mod                         ()
  HasManualNotationEdit            what             -> addFresh e hasManualNotation                      what                        ()
  AxiomatizeModuleEdit             mod              -> addFresh e axiomatizedModules                     mod                         ()
  AxiomatizeOriginalModuleNameEdit mod              -> addFresh e axiomatizedOriginalModuleNames         mod                         ()
  AxiomatizeDefinitionEdit         what             -> addFresh e axiomatizedDefinitions                 what                        ()
  UnaxiomatizeDefinitionEdit       what             -> addFresh e unaxiomatizedDefinitions               what                        ()
  AdditionalScopeEdit              place name scope -> addFresh e additionalScopes                       (place,name)                scope
  RenameEdit                       hs to            -> addFresh e renamings                              hs                          to
  ObligationsEdit                  what tac         -> addFresh e obligations                            what                        tac
  ClassKindEdit                    cls kinds        -> addFresh e classKinds                             cls                         kinds
  DataKindEdit                     dat kinds        -> addFresh e dataKinds                              dat                         kinds
  PolyKindEdit                     dat ids          -> addFresh e polyKinds                              dat                         ids
  DeleteUnusedTypeVariablesEdit    qid              -> addFresh e deleteUnusedTypeVariables              qid                         ()
  CoinductiveEdit                  ty               -> addFresh e coinductiveTypes                       ty                          ()
  RenameModuleEdit                 m1 m2            -> addFresh e renamedModules                         m1                          m2
  AliasModuleEdit{}                                 -> pure
  SimpleClassEdit                  cls              -> addFresh e simpleClasses                          cls                         ()
  InlineMutualEdit                 fun              -> addFresh e inlinedMutuals                         fun                         ()
  SetTypeEdit                      qid oty          -> addFresh e replacedTypes                          qid                         oty
  CollapseLetEdit                  qid              -> addFresh e collapsedLets                          qid                         ()
  AddEdit                          mod def ph -> return . (additions.at mod.non mempty %~ addPhase ph (definitionSentence def))
  OrderEdit                        idents           -> return . appEndo (foldMap (Endo . addEdge orders . swap) (adjacents idents))
  RewriteEdit                      rewrite          -> return . (rewrites %~ (rewrite:))
  InEdit                           qid edit         -> inEdits.at qid.non mempty %%~ addEdit edit
  PromoteEdit                      qid              -> addFresh e promotions                             qid                         ()
  PolyrecEdit                      qid              -> addFresh e polyrecs                               qid                         ()
  UniversePolymorphicEdit          qid              -> addFresh e universePolymorphic                    qid                         ()
  UniverseCumulativeEdit           qid              -> addFresh e universeCumulative                     qid                         ()
  EquationsEdit                    qid              -> addFresh e equations                              qid                         ()
  ExceptInEdit                     qids edit        -> addExceptInEdit qids edit
  InvariantEdit                    mod qid binderList cName useSigmaQids def -> addInvariantEdit mod qid binderList cName useSigmaQids def



addExceptInEdit :: MonadError String m => 
  NonEmpty Qualid -- the Qualids to which this edit should not apply
  -> Edit           -- the edit itself
  -> Edits -> m Edits
addExceptInEdit qids edit =
  
  -- add the edit globally
  -- addEditGlobally :: Edits -> m Edits
  let addEditGlobally = addEdit edit in

  -- for each qid in the list of to-be-excluded qids, add an entry (qid, edit)
  -- to the exceptInEdits map
  foldl aux addEditGlobally (toList qids)
  where
     -- f             :: Edits -> m Edits
     -- currentQidFun :: Edits -> m Edits
    aux f qid = let currentQidFun = exceptInEdits.at qid.non mempty %%~ addEdit edit in
        currentQidFun >=> f


-- "Add sentence" edit: similar to an AddEdit, but you provide a sentence
-- instead of a definition.
-- We could make a new constructor for this kind of edit (e.g. AddSentenceEdit)
-- and use addEdit to process it. But then we would have to define descDuplEdit
-- for this kind of edit, even though it would not be user facing.
-- So instead, we have the below function that accepts a Sentence and returns
-- an (Edits -> m Edits)
sentenceEdit :: MonadError String m => ModuleName -> Sentence -> Phase -> Edits -> m Edits
sentenceEdit mod sent ph = return . (additions.at mod.non mempty %~ addPhase ph sent)



-- ECG: could use case match instead
-- ECG: Note: for invariants, we only ever use the first constructor of Definition,
-- i.e. DefinitionDef
addInvariantEdit :: MonadError String m => 
     ModuleName 
  -> Qualid     -- qualid representing the type to which the invariant applies
  -> [Binder]   -- type variable binders for the type (e.g. a b c)
  -> Ident      -- the name of the constructor of the type to which the invariant applies
  -> [Qualid]   -- list of Qualids that will use the sigma type (e.g. the module export list)
  -> RocqDefinition -- the definition of the invariant
  -> Edits 
  -> m Edits
addInvariantEdit modname qid binderList constrName useSigmaQids@(_:_) def@(RocqDefinitionDef _) = 

  let useSigmaQidNE = fromList useSigmaQids
    
      defnSent = definitionSentence def
      -- invariantQualid = getDefinitionQualid dfn -- ECG: use defName?
      invariantQualid = defName def  -- e.g. Counter.NonNegInv

      -- to rename the original type to the raw type
      typeName = qualidBase qid      -- name of type to which the invariant applies, e.g. Counter
      rawTypeName = "Raw" <> typeName
      rawTypeQid = setQualidName qid rawTypeName
      typeNamespacedIdent = NamespacedIdent { niNS = TypeNS, niId = qid }
      rnTypeToRawEdit = RenameEdit typeNamespacedIdent rawTypeQid

      -- to rename the original constructor to the raw constructor
      -- (moduleNameText is defined in src/lib/HsToRocq/Util/GHC/Module.hs)
      constrQid = Qualified (moduleNameText modname) constrName       -- could use setQualidName
      rawConstrName = constrName <> "_Raw"
      rawConstrQid = Qualified (moduleNameText modname) rawConstrName -- could use setQualidName
      constrNamespacedIdent = NamespacedIdent { niNS = ExprNS, niId = constrQid }
      rnConstrToRawEdit = RenameEdit constrNamespacedIdent rawConstrQid

      -- to create the sigma type
      sigmaQid = Qualified (moduleNameText modname) ("" <> typeName)
      sigmaBoundVar = Bare "x" -- TODO: should generate fresh variable name using monad
      
      -- the type of the variable bound in the Sigma type definition
      -- (i.e. the first part of the dependent pair type)
      sigmaBVTypeParams = foldMap (toListOf binderIdents) binderList
      tyArgs = fromList $ fmap (PosArg . Qualid) sigmaBVTypeParams -- could raise an error!
      sigmaBVType = if null binderList
        then Qualid rawTypeQid
        else App (Qualid rawTypeQid) tyArgs

      sigmaArg = PosArg (Qualid sigmaBoundVar)
      sigmaPredicate = App (Qualid invariantQualid) (sigmaArg :| [])
      sigmaTerm = Sigma sigmaBoundVar (Just sigmaBVType) sigmaPredicate

      -- building the sigma type definition
      sigmaDefType = Qualid $ Bare "Type"
      sigmaDef = DefinitionDef Global sigmaQid binderList (Just sigmaDefType) sigmaTerm NotExistingClass -- ECG: is NotExistingClass correct?
      sigmaSent = DefinitionSentence sigmaDef
      

      -- creating the notation (the "constructor" for the sigma type)

      constructorName = constrName <> ""
      rawConstructorApp = App (Qualid rawConstrQid) (fromList [PosArg $ Qualid $ Bare "y"])
      -- Result: (<constructor_raw> y)
      -- TODO: should generate fresh variable name using monad

      notationFunctionName = "@existT"
      notationFunctionQid = Bare notationFunctionName
      notationTerm = App 
        (Qualid notationFunctionQid) 
        (fromList (map PosArg 
          [Underscore, Underscore, rawConstructorApp, Underscore]))
      -- Result: (@existT _ _ (<constructor_raw> y) _)

      constructorNotation = Abbreviation Local constructorName ["y"] notationTerm
      -- Result: Local Notation <constructor> y:= (@existT _ _ (<constructor_raw> y) _).

      notationSent = NotationSentence constructorNotation


      putInvDefAddEdit = sentenceEdit modname defnSent PhaseTyCl
      putSigmaDefAddEdit = sentenceEdit modname sigmaSent PhaseTyCl
      putNotationAddEdit = sentenceEdit modname notationSent PhaseTyCl
      putRnTypeToRawEdit = addEdit $ ExceptInEdit useSigmaQidNE rnTypeToRawEdit
      putRnConstrToRawEdit = addEdit $ ExceptInEdit useSigmaQidNE rnConstrToRawEdit
      editList = [putInvDefAddEdit, putSigmaDefAddEdit, putNotationAddEdit, putRnTypeToRawEdit, putRnConstrToRawEdit]
      
      in sequenceEdits editList


-- ECG: would this work: addInvariant modname = return
-- \edits -> if picky then fail else return edits
addInvariantEdit _ _ _ _ _ _ = return




sequenceEdits :: Monad m => [Edits -> m Edits] -> Edits -> m Edits
sequenceEdits = foldl (>=>) return

setQualidName :: Qualid -> Ident -> Qualid
setQualidName (Bare _) name = Bare name
setQualidName (Qualified moduleIdent _) name = Qualified moduleIdent name



defName :: RocqDefinition -> Qualid
defName (RocqDefinitionDef (DefinitionDef _ x _ _ _ _))              = x
defName (RocqDefinitionDef (LetDef          x _ _ _))                = x
defName (RocqFixpointDef   (Fixpoint    (FixBody x _ _ _ _ :| _) _)) = x
defName (RocqFixpointDef   (CoFixpoint  (FixBody x _ _ _ _ :| _) _)) = x
defName (RocqInductiveDef  (Inductive   (IndBody x _ _ _ _   :| _) _)) = x
defName (RocqInductiveDef  (CoInductive (IndBody x _ _ _ _   :| _) _)) = x
defName (RocqInstanceDef   (InstanceDefinition x _ _ _ _))           = x
defName (RocqInstanceDef   (InstanceTerm       x _ _ _ _))           = x
defName (RocqInstanceDef   (InstanceProof x _ _ _))                  = x
defName (RocqAxiomDef      (x, _))                                   = x
defName (RocqAssertionDef  (Assertion _ x _ _, _))                   = x

buildEdits :: Foldable f => f Edit -> Either String Edits
buildEdits = foldM (flip addEdit) mempty

adjacents :: NonEmpty a -> [(a,a)]
adjacents xs = zip (toList xs) (tail xs)

addFresh :: (MonadError String m, At map)
         => Edit
         -> LensLike m s t map map
         -> Index map
         -> IxValue map
         -> s
         -> m t
addFresh edit lens key val =
  lens.at key %%~ \case
    Just  _ -> throwError $ descDuplEdit edit
    Nothing -> pure $ Just val

addEdge :: (Ord k, Ord v) => ASetter' s (Map k (Set v)) -> (k, v) -> s -> s
addEdge lens (from, to) = lens %~ M.unionWith S.union (M.singleton from (S.singleton to))
