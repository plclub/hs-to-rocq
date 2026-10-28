{-|
Module      : HsToRocq.Rocq.Gallina
Description : An AST for Gallina, the surface language of Coq
Copyright   : Copyright © 2016 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental

<https://coq.inria.fr/distrib/V8.12.0/refman/language/core/. Chapter 1, \"The Gallina Specification Language\", in the Coq reference manual.>
-}

{-# LANGUAGE DeriveDataTypeable #-}

module HsToRocq.Rocq.Gallina (
  -- * Lexical structure
  -- $Lexical
  Ident,
  ModuleIdent,
  AccessIdent,
  Num,
  Op,

  -- * Terms
  -- $Terms
  Term(..),
  Arg(..),
  IfStyle(..),
  Binders,
  Generalizability(..),
  Explicitness(..),
  Binder(..),
  Name(..),
  Qualid(..),
  Sort(..),
  FixBodies(..),
  FixBody(..),
  Order(..),
  MatchItem(..),
  DepRetType(..),
  ReturnType(..),
  Equation(..),
  MultPattern(..),
  Pattern(..),
  OrPattern(..),
  Comment(..),
  LocalModule(..),

  -- * Signatures
  Signature(..),

  -- * The vernacular
  -- $Vernacular
  Sentence(..),
  EquationsDef(..),
  WfAnnotation(..),
  EquationsClause(..),
  EquationsWhere(..),
  Assumption(..),
  AssumptionKeyword(..),
  Assums(..),
  Locality(..),
  Definition(..),
  Inductive(..),
  UniverseStatus(..),
  IndBody(..),
  Fixpoint(..),
  Assertion(..),
  AssertionKeyword(..),
  Tactics,
  Proof(..),
  ImportExport(..),
  ModuleSentence(..),
  ClassDefinition(..),
  RecordDefinition(..),
  InstanceDefinition(..),
  Associativity(..),
  Level(..),
  Notation(..),
  NotationBinding(..),
  Arguments(..),
  ArgumentSpec(..),
  ArgumentExplicitness(..),
  IsExistingClass(..),

  -- * Target version
  RocqVersion(..),
  ) where

import           Prelude            hiding (Num)

import           Data.Text          (Text)
import           Numeric.Natural

import           Data.List.NonEmpty (NonEmpty ())

import           Data.Data          (Data (..))
import           Data.Typeable

-- | Target Rocq/Coq version for code generation
data RocqVersion = Rocq_8_20 | Rocq_9_0
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- $Lexical
-- <https://coq.inria.fr/distrib/V8.12.0/refman/language/core/basic.html#lexical-conventions §1.1, \"Lexical conventions\", in the Coq reference manual.>
--
-- We don't model the lexical conventions.  Values are just strings or numbers
-- or what have you.

-- |@/ident/ ::= /first_letter/ [/subsequent_letter/ … /subsequent_letter/]@
type Ident       = Text
-- |@/module_ident/ ::= /ident/ . /ident/ . …@
type ModuleIdent = Text
-- |@/access_ident/ ::= . /ident/@
type AccessIdent = Ident
-- |@/num/ ::= /digit/ … /digit/@
type Num         = Natural

-- |@/op/ ::= /symbol/ [/symbol/ … /symbol/]@ /(extra)/
type Op          = Text

-- $Terms
-- <https://coq.inria.fr/distrib/V8.12.0/refman/language/core/basic.html#essential-vocabulary \"Essential vocabulary\", in the Coq reference manual.>

-- |NB: There is a bug in the Coq manual as regards the definition
-- of destructuring pattern-@let@, i.e. with @let ' /pattern/ …@.  The
-- definition is given as
--
-- @
-- let ' /pattern/ [in /term/] := /term/ [/return_type/] in /term/
-- @
--
-- However:
--
-- 1. The @in@ annotation will only parse if the @/return_type/@ is present; and
-- 2. The @in@ annotation should be @[in /qualid/ [/pattern/ … /pattern/]]@
--    instead of simply @[in /term/]@, just as for @/match_item/@.
--
-- I have thus implemented this change in the AST that follows (the 'LetTick'
-- and 'LetTickDep' cases).
--
-- @/term/ ::=@
data Term = Forall Binders Term                                                                -- ^@forall /binders/, /term/@
          | Fun Binders Term                                                                   -- ^@fun /binders/ => /term/@
          | Fix FixBodies                                                                      -- ^@fix /fix_bodies/@
          | Cofix FixBodies                                                                    -- ^@cofix /cofix_bodies/@
          | Let Qualid [Binder] (Maybe Term) Term Term                                         -- ^@let /ident/ [/binders/] [: /term/] := /term/ in /term/@
          | LetTuple [Name] (Maybe DepRetType) Term Term                                       -- ^@let ( [/name/ , … , /name/] ) [/dep_ret_type/] := /term/ in /term/@
          | LetTick Pattern Term Term                                                          -- ^@let ' /pattern/ := /term/ in /term/@
          | If IfStyle Term (Maybe DepRetType) Term Term                                       -- ^@if /term/ [/dep_ret_type/] then /term/ else /term/@
          | HasType Term Term                                                                  -- ^@/term/ : /term/@
          | CheckType Term Term                                                                -- ^@/term/ <: /term/@
          | ToSupportType Term                                                                 -- ^@/term/ :>@
          | Arrow Term Term                                                                    -- ^@/term/ -> /term/@
          | App Term (NonEmpty Arg)                                                            -- ^@/term/ /arg/ … /arg/@
          | ExplicitApp Qualid [Term]                                                          -- ^@\@ /qualid/ [/term/ … /term/]@
          | InScope Term Ident                                                                 -- ^@/term/ % /ident/@
          | Match (NonEmpty MatchItem) (Maybe ReturnType) [Equation]                           -- ^@match /match_item/ , … , /match_item/ [/return_type/] with [[|] /equation/ | … | /equation/] end@
          | Qualid Qualid                                                                      -- ^@/qualid/@
          | RawQualid Qualid                                                                   -- ^@/qualid/@ like Qualid, but never printed with notation
          | Sort Sort                                                                          -- ^@/sort/@
          | Num Num                                                                            -- ^@/num/@
          | String Text                                                                        -- ^@/string/@ – extra (holds the value, not the source text)
          | HsString Text                                                                      -- ^@& /string/@ – extra (for Haskell string literals)
          | HsChar Char                                                                        -- ^@&# /string/@ – extra (for Haskell character literals; /string/ is a single ASCII character)
          | Underscore                                                                         -- ^@_@
          | Parens Term                                                                        -- ^@( /term/ )@
          | Bang Term                                                                          -- ^@! term - tmp suppress implicit arguments (for Instance decls)
          | Record [ (Qualid, Term) ]                                                          -- ^@{| /qualid/ := /term/; … |}@
          | Sigma Qualid (Maybe Term) Term                                                     -- ^@{ /ident/ [: /term/] & /term/ }@
          deriving (Eq, Ord, Show, Read, Typeable, Data)

infixr 7 `Arrow`
infixl 8 `App`

data IfStyle = SymmetricIf | LinearIf -- LinearIf is used for guards, to avoid adding indentation
          deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/arg/ ::=@
data Arg = PosArg Term                                                                         -- ^@/term/@
         | NamedArg Ident Term                                                                 -- ^@( /ident/ := /term/ )@
         deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/binders/ ::= /binder/ … /binder/@
type Binders = NonEmpty Binder

-- |@/generalizability/ ::=@ – not a part of the grammar /per se/, but a common fragment
data Generalizability = Ungeneralizable                                                        -- ^@@ – (nothing)
                      | Generalizable                                                          -- ^@`@
                      deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/explicitness/ ::=@ – not a part of the grammar /per se/, but a common fragment
data Explicitness = Explicit                                                                   -- ^@( ⋯ )@ – wrap in parentheses
                  | Implicit                                                                   -- ^@{ ⋯ }@ – wrap in braces
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/binder/ ::=@ – the @/explicitness/@ is extra
--
-- https://coq.inria.fr/distrib/V8.12.0/refman/language/core/assumptions.html#grammar-token-binder
data Binder = ExplicitBinder Name                                                              -- ^@/name/@ (inferred type)
            | ImplicitBinders (NonEmpty Name)                                                  -- ^@{/name/ ... /name/}@ (inferred type)
            | Typed Generalizability Explicitness (NonEmpty Name) Term                         -- ^@generalizability/ ( /name/ … /name/ : /term/ )@ or @/generalizability/ { /name/ … /name/ : /term/ }@
            | Generalized Explicitness Term                                                    -- ^@` ( /term/ )@ or @` { /term/ }@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/name/ ::=@
data Name = Ident Qualid                                                                       -- ^@/ident/@
          | UnderscoreName                                                                     -- ^@_@
          deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/qualid/ ::=@
data Qualid = Bare Ident                                                                       -- ^@/ident/@
            | Qualified ModuleIdent AccessIdent                                                -- ^@/module_ident/ /access_ident/@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/sort/ ::=@
data Sort = Prop                                                                               -- ^@Prop@
          | Set                                                                                -- ^@Set@
          | Type                                                                               -- ^@Type@
          deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/fix_bodies/ ::=@
data FixBodies = FixOne FixBody                                                                -- ^@/fix_body/@
               | FixMany FixBody (NonEmpty FixBody) Qualid                                     -- ^@/fix_body/ with /fix_body/ with … with /fix_body/ for /ident/@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/fix_body/ ::=@
data FixBody = FixBody Qualid Binders (Maybe Order) (Maybe Term) Term                     -- ^@/ident/ /binders/ [/order/] [: /term/] := /term/@
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/annotation/ ::=@
data Order = StructOrder Qualid                                                                -- ^@{ struct /ident/ }@
           | MeasureOrder Term (Maybe Term)                                                    -- ^@measure /term/ (/term/)?/
           | WFOrder Term Qualid                                                               -- ^@wf /term/ /ident//
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/match_item/ ::=@
data MatchItem = MatchItem Term (Maybe Name) (Maybe (Qualid, [Pattern]))                       -- ^@/term/ [as /name/] [in /qualid/ [/pattern/ … /pattern/]]@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/dep_ret_type/ ::=@
data DepRetType = DepRetType (Maybe Name) ReturnType                                           -- ^@[as /name/] /return_type/@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/return_type/ ::=@
newtype ReturnType = ReturnType Term                                                           -- ^@return /term/@
                   deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/equation/ ::=@
data Equation = Equation (NonEmpty MultPattern) Term                                           -- ^@/mult_pattern/ | … | /mult_pattern/ => /term/@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/mult_pattern/ ::=@
newtype MultPattern = MultPattern (NonEmpty Pattern)                                           -- ^@/pattern/ , … , /pattern/@
                    deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/pattern/ ::=@
data Pattern = ArgsPat Qualid [Pattern]                                               -- ^@/qualid/ /pattern/ … /pattern/@ – should start with a constructor
             | ExplicitArgsPat Qualid (NonEmpty Pattern)                                       -- ^@\@ /qualid/ /pattern/ … /pattern/@
             | InfixPat Pattern Op Pattern                                                     -- ^@/pattern/ /op/ /pattern/@ – extra
             | AsPat Pattern Qualid                                                            -- ^@/pattern/ as /ident/@
             | InScopePat Pattern Ident                                                        -- ^@/pattern/ % /ident/@
             | QualidPat Qualid                                                                -- ^@/qualid/@ – should be only variables
             | UnderscorePat                                                                   -- ^@_@
             | NumPat Num                                                                      -- ^@/num/@
             | StringPat Text                                                                  -- ^@/string/@ – extra (holds the value, not the source text)
             | OrPats (NonEmpty OrPattern)                                                     -- ^@( /or_pattern/ , … , /or_pattern/ )@
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/or_pattern/ ::=@
newtype OrPattern = OrPattern (NonEmpty Pattern)                                               -- ^@/pattern/ | … | /pattern/@
                  deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/comment/ ::=@ /(extra)/
newtype Comment = Comment Text                                                                 -- ^@(* … *)@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- $Vernacular
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#Vernacular §1.3, \"The Vernacular\", in the Coq reference manual.>.
-- Module stuff is from <https://coq.inria.fr/refman/Reference-Manual004.html#Import §2.5, \"Module system\">,
-- and @Require@ is from <https://coq.inria.fr/refman/Reference-Manual008.html#Require §6.5.1>.
--
-- We also add cases to deal with certain notation definitions and similar.

data IsExistingClass = ExistingClass | NotExistingClass
         deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/sentence/ ::=@
data Sentence = AssumptionSentence       Assumption                                            -- ^@/assumption/@
              | DefinitionSentence       Definition                                            -- ^@/definition/@
              | InductiveSentence        Inductive                                             -- ^@/inductive/@
              | FixpointSentence         Fixpoint                                              -- ^@/fixpoint/@
              | ProgramSentence          Sentence (Maybe Text)                                 -- ^@Program /sentence/ Solve Obligations with (/tac/). Admit Obligations.@
              | AssertionSentence        Assertion Proof                                       -- ^@/assertion/ /proof/@
              | ModuleSentence           ModuleSentence                                        -- ^@/module_sentence/@ – extra (inferred from §2.5)
              | ClassSentence            ClassDefinition                                       -- ^@/class_definition/@ – extra
--              | ExistingClassSentence    Qualid                                                -- ^@/Existing Class /ident//@ – extra
              | RecordSentence           RecordDefinition                                      -- ^@/class_definition/@ – extra
              | InstanceSentence         InstanceDefinition                                    -- ^@/instance_definition/@ – extra
              | NotationSentence         Notation                                              -- ^@/notation/@ – extra
              | ArgumentsSentence        Arguments                                             -- ^@/arguments/@ – extra
              | CommentSentence          Comment                                               -- ^@/comment/@ – extra
              | LocalModuleSentence      LocalModule
              | EquationsSentence        EquationsDef                                          -- ^@Equations …@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@Equations /name/ /binders/ : /retTy|_/ [by wf (/measure/) /relation/] := /name/ /pat/ … := /rhs/ ; … [where /name/ /binders/ : /retTy/ := …] .@
--
-- When @retTy@ is absent, @_@ is emitted (Coq infers the type).
-- Does not model @Equations?@, @noind@, @transparent@, or recursive
-- where-clauses with @wf@ — these Equations plugin features are unsupported.
data EquationsDef = EquationsDef
  { eqnName    :: Qualid                                 -- ^Function name
  , eqnBinders :: Binders                                -- ^Binders (non-empty; annotated with types when available)
  , eqnRetType :: Maybe Term                             -- ^Return type (emitted as @_@ when 'Nothing')
  , eqnWf      :: Maybe WfAnnotation                      -- ^Optional @by wf (measure) relation@
  , eqnClauses :: NonEmpty EquationsClause               -- ^Equation clauses (non-empty)
  , eqnWheres  :: [EquationsWhere]                       -- ^Where clauses for local helpers
  } deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |Well-founded recursion annotation: @by wf (measure) relation@.
data WfAnnotation = WfAnnotation
  { wfMeasure  :: Term    -- ^The measure expression
  , wfRelation :: Qualid  -- ^The well-founded relation (e.g., @lt@)
  } deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |A single equation clause: patterns on the LHS and a term on the RHS.
data EquationsClause = EquationsClause
  { ecPats :: NonEmpty Pattern  -- ^LHS patterns (count should match explicit binder count in enclosing 'EquationsDef')
  , ecRHS  :: Term              -- ^RHS body
  } deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@Equations@ where clause for auxiliary definitions.
-- Uses @[Binder]@ (not @Binders@) because where clauses can have zero explicit
-- binders when only a full type annotation is provided (e.g., @where helper : bool -> bool :=@).
data EquationsWhere = EquationsWhere
  { ewName    :: Qualid               -- ^Helper function name
  , ewBinders :: [Binder]             -- ^Typed binders (may be empty)
  , ewRetType :: Maybe Term           -- ^Return type
  , ewClauses :: NonEmpty EquationsClause  -- ^Equation clauses (non-empty)
  } deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assumption/ ::=@
data Assumption = Assumption AssumptionKeyword Assums                                          -- ^@/assumption_keyword/ /assums/ .@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assumption_keyword/ ::=@
data AssumptionKeyword = Axiom                                                                 -- ^@Axiom@
                       | Axioms                                                                -- ^@Axioms@ – not in the grammar, but accepted.
                       | Conjecture                                                            -- ^@Conjecture@
                       | Parameter                                                             -- ^@Parameter@
                       | Parameters                                                            -- ^@Parameters@
                       | Variable                                                              -- ^@Variable@
                       | Variables                                                             -- ^@Variables@
                       | Hypothesis                                                            -- ^@Hypothesis@
                       | Hypotheses                                                            -- ^@Hypotheses@
                       deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/assums/ ::=@
data Assums = Assums (NonEmpty Qualid) Term                                     -- ^@/ident/ … /ident/ : /term/@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@[Local] ::=@ – not a part of the grammar /per se/, but a common fragment.
-- Coq 8.20 replaced keyword locality (Global/Local) with attribute-based
-- locality (#[global]/#[local]/#[export]). ExportL added as the new default
-- (previously Global served as the no-locality case).
data Locality = ExportL                                                                        -- ^@@ – (nothing – but sometimes @Export@)
              | Global                                                                         -- ^@Global@
              | Local                                                                          -- ^@Local@
              deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/definition/ ::=@
data Definition = DefinitionDef Locality Qualid [Binder] (Maybe Term) Term IsExistingClass     -- ^@[Local] Definition /ident/ [/binders/] [: /term/] := /term/ .@
                | LetDef Qualid [Binder] (Maybe Term) Term                                     -- ^@Let /ident/ [/binders/] [: /term/] := /term/ .@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/inductive/ ::=@ – the @where@ notation bindings are extra
data Inductive = Inductive   (NonEmpty IndBody) [NotationBinding]                              -- ^@Inductive /ind_body/ with … with /ind_body/ [where /notation_binding/ and … and /notation_binding/] .@
               | CoInductive (NonEmpty IndBody) [NotationBinding]                              -- ^@CoInductive /ind_body/ with … with /ind_body/ [where /notation_binding/ and … and /notation_binding/] .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |Universe polymorphism and cumulativity flags for inductive types.
data UniverseStatus = NotUnivPoly         -- ^Monomorphic (default)
                    | UnivPoly            -- ^@#[universes(polymorphic)]@
                    | UnivPolyCumulative  -- ^@#[universes(polymorphic, cumulative)]@
                    deriving (Eq, Show, Read, Typeable, Data)

-- | Explicit 'Ord' instance encoding the universe subsumption lattice:
-- @NotUnivPoly < UnivPoly < UnivPolyCumulative@.  Used by 'maximum' in
-- "HsToRocq.Rocq.Pretty" to merge statuses across a mutual inductive block.
instance Ord UniverseStatus where
  compare a b = compare (rank a) (rank b)
    where rank :: UniverseStatus -> Int
          rank NotUnivPoly        = 0
          rank UnivPoly           = 1
          rank UnivPolyCumulative = 2

-- |@/ind_body/ ::=@
data IndBody = IndBody Qualid [Binder] Term [(Qualid, [Binder], Maybe Term)] UniverseStatus -- ^@/ident/ [/binders/] : /term/ := [[|] /ident/ [/binders/] [: /term/] | … | /ident/ [/binders/] [: /term/]]@; 'UniverseStatus' is an hs-to-rocq extension
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/fixpoint/ ::=@
data Fixpoint = Fixpoint   (NonEmpty FixBody)   [NotationBinding]                              -- ^@Fixpoint /fix_body/ with … with /fix_body/ [where /notation_binding/ and … and /notation_binding/] .@
              | CoFixpoint (NonEmpty FixBody) [NotationBinding]                                -- ^@CoFixpoint /fix_body/ with … with /fix_body/ [where /notation_binding/ and … and /notation_binding/] .@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assertion/ ::=@
data Assertion = Assertion AssertionKeyword Qualid [Binder] Term                               -- ^@/assertion_keyword/ /ident/ [/binders/] : /term/ .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assertion_keyword/ ::=@
data AssertionKeyword = Theorem                                                                -- ^@Theorem@
                      | Lemma                                                                  -- ^@Lemma@
                      | Remark                                                                 -- ^@Remark@
                      | Fact                                                                   -- ^@Fact@
                      | Corollary                                                              -- ^@Corollary@
                      | Proposition                                                            -- ^@Proposition@
                      | Definition                                                             -- ^@Definition@
                      | Example                                                                -- ^@Example@
                      deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |A \"representation\" of tactics; left as @…@ in the grammar
type Tactics = Text

-- |@/proof/ ::=@
data Proof = ProofQed      Tactics                                                             -- ^@Proof . … Qed .@
           | ProofDefined  Tactics                                                             -- ^@Proof . … Defined .@
           | ProofAdmitted Tactics                                                             -- ^@Proof . … Admitted .@
           deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/import_export/@ ::= – extra (inferred from §2.5.8)
data ImportExport = Import                                                                     -- ^@Import@
                  | Export                                                                     -- ^@Export@
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/module_sentence/@ ::= – extra (inferred from §2.5 and §6.5.1), and incomplete
data ModuleSentence = ModuleImport ImportExport (NonEmpty ModuleIdent)                         -- ^@/import_export/ /qualid/ … /qualid/ .@
                    | Require (Maybe ModuleIdent) (Maybe ImportExport) (NonEmpty ModuleIdent)  -- ^@[From /qualid/] Require [/import_export/] /qualid/ … /qualid/ .@
                    | ModuleAssignment ModuleIdent ModuleIdent                                 -- ^@Module /qualid/ := /qualid/ .@
                    deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/class_definition/ ::=@ /(extra)/
data ClassDefinition = ClassDefinition Qualid [Binder] (Maybe Sort) [(Qualid, Term)]            -- ^@Class /ident/ [/binders/] [: /sort/] := { [/ident/ : /term/ ; … ; /ident/ : /term/] } .
                     deriving (Eq, Ord, Show, Read, Typeable, Data)
                     -- TODO: field arguments (which become @forall@ed)

-- |@/record_definition/ ::=@ /(extra)/
data RecordDefinition = RecordDefinition Qualid [Binder] (Maybe Sort) (Maybe Qualid) [(Qualid, Term)]  -- ^@Record /ident/ [/binders/] [: /sort/] := /ident/ { [/ident/ : /term/ ; … ; /ident/ : /term/] } .
                     deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/instance_definition/ ::=@ /(extra)/
data InstanceDefinition = InstanceDefinition Qualid [Binder] Term [(Qualid, Term)] (Maybe Proof) -- ^@Instance /ident/ [/binders/] : /term/ := { [/ident/ := /term/ ; … ; /ident/ := /term/] } [/proof/] .
                                                                                                 -- TODO: field arguments (which become @fun@ arguments)
                        | InstanceTerm Qualid [Binder] Term Term (Maybe Proof)                   -- ^@Instance /ident/ [/binders/] : /term/ := /term/ [/proof/] .
                        | InstanceProof Qualid [Binder] Term Proof                               -- ^@Instance /ident/ [/binders/] : /term/. /proof/
                        deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/associativity/ ::=@ /(extra)/
data Associativity = LeftAssociativity                                                         -- ^@left@
                   | RightAssociativity                                                        -- ^@right@
                   | NoAssociativity                                                           -- ^@no@
                   deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/level/ ::=@ /(extra)/
newtype Level = Level Num                                                                      -- ^@at level /num/@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/notation/ ::=@ /(extra)/
data Notation = ReservedNotationIdent Ident                                                    -- ^@Reserved Notation "'/ident/'" .@
              | NotationBinding NotationBinding                                                -- ^@Notation /notation_binding/ .@
              | InfixDefinition Op Term (Maybe Associativity) Level                            -- ^@Infix "/op/" := ( /term/ ) ( [/associativity/ associativity ,] /level/ ) .@
              | Abbreviation Locality Ident [Ident] Term                                       -- ^@[Local] Notation /ident/ [: /ident/] := /term/ .@   
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/notation_binding/ ::=@ /(extra)/
data NotationBinding = NotationIdentBinding Ident Term                                         -- ^@"'/ident/'" := (/term/) .@
                     deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/arguments/ ::=@ /(extra)/
data Arguments = Arguments (Maybe Locality) Qualid [ArgumentSpec]                              -- ^@[Local|Global]@ Arguments /qualid/ [/argument_spec/ … /argument_spec/] .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/argument_spec/ ::=@ /(extra)/
data ArgumentSpec = ArgumentSpec ArgumentExplicitness Name (Maybe Ident)                       -- ^@/name/ [% /ident/]@ or @[ /name/ ] [% /ident/]@ or @{ /name/ } [% /ident/]@
                  deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/argument_explicitness/ ::=@ /(extra)/ – not a part of the grammar /per se/, but a common fragment
data ArgumentExplicitness = ArgExplicit                                                        -- ^@( ⋯ )@ – wrap in parentheses or nothing
                          | ArgImplicit                                                        -- ^@[ ⋯ ]@ – wrap in square brackets
                          | ArgMaximal                                                         -- ^@{ ⋯ }@ – wrap in braces
                          deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)


data LocalModule = LocalModule Ident [Sentence]
                      deriving (Eq, Ord, Show, Read, Typeable, Data)

-- A Coq signature
-- TODO: Move this?
data Signature = Signature { sigType   :: Term
                           , sigFixity :: Maybe (Associativity, Level) }
               deriving (Eq, Ord, Show, Read, Typeable, Data)
