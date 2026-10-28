{-# LANGUAGE PatternSynonyms, OverloadedStrings, LambdaCase, TemplateHaskell, ViewPatterns #-}

module HsToRocq.Rocq.Gallina.Util (
  -- * Common AST patterns
  pattern Var,    pattern App1,    pattern App2,    pattern App3,    appList,
  pattern VarPat, pattern App1Pat, pattern App2Pat, pattern App3Pat,
  pattern BName,
  mkInfix,
  maybeForall,
  maybeFun,
  pattern IfBool, pattern IfCase,
  pattern LetFix, pattern LetCofix,
  collectArgs,
  collectBinders,

  -- * Manipulating 'Term's
  termHead,

  -- * Manipulating 'FixBody's
  fixBodyName, fixBodyArgs, fixBodyTermination, fixBodyResultType, fixBodyBody,

  -- * Manipulating 'Binder's, 'Name's, and 'Qualid's
  -- ** Manipulating one 'Binder' at a time, even when the 'Typed' case has multiple names
  BinderSplit(..), caseOneBinder,
  unconsOneBinder, unconsOneBinderFromType,
  BinderInfo(..), biGeneralizability, biExplicitness, biMaybeName, biMaybeType,
  -- ** Optics
  _Ident, _UnderscoreName, nameToIdent,
  binderNames, binderIdents, binderExplicitness, binderGeneralizability,
  mkBinder, mkBinders, mkTypedBinder, toImplicitBinder, toExplicitBinder,
  -- ** Functions
  qualidBase, qualidModule, qualidMapBase, qualidExtendBase,
  splitModule,
  qualidToIdent, identToQualid, identToBase,
  qualidIsOp, qualidHasValidRocqOp, qualidToOp, qualidToPrefix,
  unsafeIdentToQualid,
  nameToTerm, nameToPattern,
  binderArgs,
  consolidateTypedBinders,
  normalizeType,

  -- * Manipulating 'Sentence's
  isComment,

  -- * Version-conditional rewriting
  coqToStdlib,
  rocq9RewriteText,
  rewriteTextFor,
  rewriteASTFor,
  ) where

import Control.Lens

import Data.Bifunctor
import Data.Semigroup ((<>))
import Data.Char (GeneralCategory(NonSpacingMark), generalCategory, isAlphaNum, isDigit, isHexDigit, isLetter, isSpace)
import Data.Foldable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.List.NonEmpty as NEL

import qualified Data.Text as T
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Data (Data)
import Data.Generics (everywhere, mkT, extT)
import GHC.Stack

import HsToRocq.Util.Monad (ErrorString)
import HsToRocq.Rocq.Gallina
import HsToRocq.ConvertHaskell.InfixNames

pattern Var  :: Ident                        -> Term
pattern App1 :: Term -> Term                 -> Term
pattern App2 :: Term -> Term -> Term         -> Term
pattern App3 :: Term -> Term -> Term -> Term -> Term
appList      :: Term -> [Arg]                -> Term

pattern Var  x          = Qualid (Bare x)
pattern App1 f x        = App f (PosArg x :| [])
pattern App2 f x1 x2    = App f (PosArg x1 :| PosArg x2 : [])
pattern App3 f x1 x2 x3 = App f (PosArg x1 :| PosArg x2 : PosArg x3 : [])
appList      f          = maybe f (App f) . nonEmpty

pattern VarPat  :: Ident                                   -> Pattern
pattern App1Pat :: Qualid -> Pattern                       -> Pattern
pattern App2Pat :: Qualid -> Pattern -> Pattern            -> Pattern
pattern App3Pat :: Qualid -> Pattern -> Pattern -> Pattern -> Pattern

pattern VarPat  x          = QualidPat (Bare x)
pattern App1Pat c x        = ArgsPat c [x]
pattern App2Pat c x1 x2    = ArgsPat c [x1, x2]
pattern App3Pat c x1 x2 x3 = ArgsPat c [x1, x2, x3]

pattern BName :: Ident -> Name
pattern BName  x          = Ident (Bare x)

-- Legacy combinator, to migrate away from the Infix constructor
mkInfix :: Term -> Qualid -> Term -> Term
mkInfix l op = App2 (Qualid op) l

maybeForall :: Foldable f => f Binder -> Term -> Term
maybeForall = maybe id Forall . nonEmpty . toList
{-# INLINABLE  maybeForall #-}
{-# SPECIALIZE maybeForall :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeForall :: NonEmpty Binder -> Term -> Term #-}

maybeFun :: Foldable f => f Binder -> Term -> Term
maybeFun = maybe id Fun . nonEmpty . toList
{-# INLINABLE  maybeFun #-}
{-# SPECIALIZE maybeFun :: [Binder]        -> Term -> Term #-}
{-# SPECIALIZE maybeFun :: NonEmpty Binder -> Term -> Term #-}

-- Two possible desugarings of if-then-else
pattern IfBool :: IfStyle -> Term -> Term -> Term -> Term
pattern IfBool is c t e = If is (HasType c (Var "bool")) Nothing t e

pattern IfCase :: IfStyle -> Term -> Term -> Term -> Term
pattern IfCase is c t e = If is (App1 (Var "Bool.Sumbool.sumbool_of_bool") c) Nothing t e

isLetFix :: Term -> Maybe (FixBody, Term)
isLetFix (Let f [] Nothing (Fix (FixOne fb@(FixBody f' _ _ _ _))) body)
    | f == f'   = Just (fb, body)
isLetFix _ = Nothing

pattern LetFix :: FixBody -> Term -> Term
pattern LetFix fb body <- (isLetFix -> Just (fb, body))
  where LetFix fb@(FixBody f _ _ _ _) body = Let f [] Nothing (Fix (FixOne fb)) body

isLetCofix :: Term -> Maybe (FixBody, Term)
isLetCofix (Let f [] Nothing (Cofix (FixOne fb@(FixBody f' _ _ _ _))) body)
    | f == f'   = Just (fb, body)
isLetCofix _ = Nothing

pattern LetCofix :: FixBody -> Term -> Term
pattern LetCofix fb body <- (isLetCofix -> Just (fb, body))
  where LetCofix fb@(FixBody f _ _ _ _) body = Let f [] Nothing (Cofix (FixOne fb)) body

termHead :: Term -> Maybe Qualid
termHead (Forall _ t)         = termHead t
termHead (HasType t _)        = termHead t
termHead (CheckType t _)      = termHead t
termHead (ToSupportType t)    = termHead t
termHead (Parens t)           = termHead t
termHead (InScope t _)        = termHead t
termHead (App t _)            = termHead t
termHead (ExplicitApp name _) = Just name
termHead (Qualid name)        = Just name
termHead _                    = Nothing

fixBodyName :: Lens' FixBody Qualid
fixBodyName = lens (\(FixBody name _ _ _ _) -> name)
                   (\(FixBody _ args mord mty body) name -> FixBody name args mord mty body)

fixBodyArgs :: Lens' FixBody Binders
fixBodyArgs = lens (\(FixBody _ args _ _ _) -> args)
                   (\(FixBody name _ mord mty body) args -> FixBody name args mord mty body)

fixBodyTermination :: Lens' FixBody (Maybe Order)
fixBodyTermination = lens (\(FixBody _ _ mord _ _) -> mord)
                   (\(FixBody name args _ mty body) mord -> FixBody name args mord mty body)

fixBodyResultType :: Lens' FixBody (Maybe Term)
fixBodyResultType = lens (\(FixBody _ _ _ mty _) -> mty)
                   (\(FixBody name args mord _ body) mty -> FixBody name args mord mty body)

fixBodyBody :: Lens' FixBody Term
fixBodyBody = lens (\(FixBody _ _ _ _ body) -> body)
                   (\(FixBody name args mord mty _) body -> FixBody name args mord mty body)


makePrisms ''Name

nameToIdent :: Iso' Name (Maybe Qualid)
nameToIdent = iso (\case Ident x        -> Just x
                         UnderscoreName -> Nothing)
                  (maybe UnderscoreName Ident)
{-# INLINEABLE nameToIdent #-}

binderNames :: Traversal' Binder Name
binderNames f (ExplicitBinder name) = ExplicitBinder <$> f name
binderNames f (ImplicitBinders names) = ImplicitBinders <$> traverse f names
binderNames f (Typed gen ei names ty) = traverse f names <&> \names' -> Typed gen ei names' ty
binderNames _ gen@Generalized{} = pure gen
{-# INLINEABLE binderNames #-}

binderIdents :: Traversal' Binder Qualid
binderIdents = binderNames._Ident
{-# INLINEABLE binderIdents #-}

binderExplicitness :: Binder -> Explicitness
binderExplicitness = \case
  ExplicitBinder  _ -> Explicit
  ImplicitBinders _ -> Implicit
  Typed _ ei _ _ -> ei
  Generalized ei _ -> ei
{-# INLINEABLE binderExplicitness #-}

toImplicitBinder :: Binder -> Binder
toImplicitBinder (ExplicitBinder name) = ImplicitBinders (pure name)
toImplicitBinder b@(ImplicitBinders _) = b
toImplicitBinder (Typed ex _ei names ty) = Typed ex Implicit names ty
toImplicitBinder (Generalized _ei ty) = Generalized Implicit ty

-- | Convert a binder to explicit. Coq 8.20 warns about implicit binders
-- inside record literals ({| field := fun {a} => ... |}); use this to suppress.
toExplicitBinder :: Binder -> Binder
toExplicitBinder b@(ExplicitBinder _) = b
toExplicitBinder (ImplicitBinders names) = ImplicitBinders names  -- no type info; keep as-is
toExplicitBinder (Typed ex _ei names ty) = Typed ex Explicit names ty
toExplicitBinder (Generalized _ei ty) = Generalized Explicit ty

-- | Single-name binder with inferred type. (Drops parentheses if Explicit.)
mkBinder :: Explicitness -> Name -> Binder
mkBinder Explicit name = ExplicitBinder name
mkBinder Implicit name = ImplicitBinders (pure name)

-- | Multi-name binder with explicit type.
mkBinders :: Explicitness -> NonEmpty Name -> Term -> Binder
mkBinders = Typed Ungeneralizable

mkTypedBinder :: Explicitness -> Name -> Term -> Binder
mkTypedBinder ex n = Typed Ungeneralizable ex (n :| []) 

binderGeneralizability :: Binder -> Generalizability
binderGeneralizability = \case
  ExplicitBinder  _ -> Ungeneralizable
  ImplicitBinders _ -> Ungeneralizable
  Typed gen _ _ _ -> gen
  Generalized _ _ -> Generalizable
{-# INLINEABLE binderGeneralizability #-}

qualidBase :: Qualid -> Ident
qualidBase (Bare      ident) = ident
qualidBase (Qualified _ aid) = aid

qualidModule :: Qualid -> Maybe ModuleIdent
qualidModule (Bare      _)     = Nothing
qualidModule (Qualified qid _) = Just qid

-- | Apply a function to the last component (base name) of a qualified name.
qualidMapBase :: (Ident -> Ident) -> Qualid -> Qualid
qualidMapBase f (Bare             base) = Bare             $ f base
qualidMapBase f (Qualified prefix base) = Qualified prefix $ f base

qualidExtendBase :: T.Text -> Qualid -> Qualid
qualidExtendBase suffix = qualidMapBase (<> suffix)

qualidToIdent :: Qualid -> Ident
qualidToIdent (Bare      ident)   = ident
qualidToIdent (Qualified qid aid) = qid <> "." <> aid

qualidIsOp :: Qualid -> Bool
qualidIsOp = identIsOp . qualidBase

-- | Check if the decoded operator uses only valid Coq operator characters.
-- Coq symbols consist of: + - * / \ < > = ~ ! @ # % ^ & | : ? , and Unicode symbols.
-- Characters like '$' are not valid.
qualidHasValidRocqOp :: Qualid -> Bool
qualidHasValidRocqOp qid = case identToOp (qualidBase qid) of
  Nothing -> False
  Just op -> T.all isValidRocqOpChar op
             && not (isAmbiguousRocqOp op)
  where
    isValidRocqOpChar c = c `elem` ("+-*/\\<>=~!@#%^&|:?," :: [Char])
                      || c > '\x7f'  -- Unicode symbols
    -- Operators that start with a built-in operator prefix create ambiguity
    -- when qualified (e.g., "GHC.Base.<*" parses as "GHC.Base.<" then "*").
    isAmbiguousRocqOp op = op == "<*"

qualidToOp :: Qualid -> Maybe Op
qualidToOp (Qualified qid aid) = ((qid <> ".") <>) <$> identToOp aid
qualidToOp (Bare aid)          =                       identToOp aid

qualidToPrefix :: Qualid -> Maybe Op
qualidToPrefix qid = infixToPrefix <$> qualidToOp qid


-- This doesn't handle all malformed 'Ident's
identToQualid :: HasCallStack => Ident -> Maybe Qualid
identToQualid x = case splitModule x of
    Just (mod, ident) -> Just (Qualified mod (toPrefix ident))
    _                 -> Just (Bare (toPrefix x))

identToBase :: Ident -> Ident
identToBase x = maybe x qualidBase $ identToQualid x

nameToTerm :: Name -> Term
nameToTerm (Ident x)      = Qualid x
nameToTerm UnderscoreName = Underscore

nameToPattern :: Name -> Pattern
nameToPattern (Ident x)      = QualidPat x
nameToPattern UnderscoreName = UnderscorePat

binderArgs :: Foldable f => f Binder -> [Arg]
binderArgs = map (PosArg . nameToTerm) . foldMap (toListOf binderNames)
           . filter (\b -> binderExplicitness b == Explicit) . toList


unsafeIdentToQualid :: HasCallStack => Ident -> Qualid
unsafeIdentToQualid i = fromMaybe (error $ "unsafeIdentToQualid: " ++ show i) (identToQualid i)

collectArgs :: Term -> Either ErrorString (Qualid, [Term])
collectArgs (Qualid qid) = return (qid, [])
collectArgs (App t args) = do
    (f, args1) <- collectArgs t
    args2 <- mapM fromArg (toList args)
    return (f, args1 ++ args2)
  where
    fromArg (PosArg t) = return t
    fromArg _          = Left "non-positional argument"
collectArgs (Arrow a1 a2) = return (arrow_qid, [a1, a2])
  where arrow_qid = Qualified "GHC.Prim" "arrow"
collectArgs (Parens t)    = collectArgs t
collectArgs (InScope t _) = collectArgs t
collectArgs (HasType t _) = collectArgs t
collectArgs t             = Left $ "collectArgs: " ++ show t

-- assuming that the term is in prenex normal form
collectBinders :: Term -> [Binder]
collectBinders (Forall bs t) = do
  toList bs ++ collectBinders t
collectBinders _ = []

consolidateTypedBinders :: Binders -> Binders
consolidateTypedBinders (Typed g1 ei1 xs1 t1 :| Typed g2 ei2 xs2 t2 : bs) | g1 == g2 , ei1 == ei2 , t1 == t2 =
  consolidateTypedBinders (Typed g1 ei1 (xs1 <> xs2) t1 :| bs)
consolidateTypedBinders (b1 :| b2 : bs) =
  b1 NEL.<| consolidateTypedBinders (b2 :| bs)
consolidateTypedBinders (b :| []) =
  b :| []

data BinderSplit
  = Binder_ Generalizability Explicitness Name (Maybe Term) (Maybe Binder)
  | Generalized_ Explicitness Term

-- |Case analysis on a 'Binder', but pulls out a single case from a
-- multiple-names-with-the-same-type binder.  (E.g., @x@ becomes @x@, @(x : t)@
-- becomes @(x : t)@, but @(x y z : t)@ becomes @(x : t)@ plus @(y z : t)@.)
caseOneBinder :: Binder -> BinderSplit
caseOneBinder (ExplicitBinder name) = Binder_ Ungeneralizable Explicit name Nothing Nothing
caseOneBinder (ImplicitBinders (name :| names)) =
  let rest = ImplicitBinders <$> nonEmpty names in
  Binder_ Ungeneralizable Implicit name Nothing rest
caseOneBinder (Typed g ei (name :| names) ty) =
  let rest = nonEmpty names <&> \names -> Typed g ei names ty in
  Binder_ g ei name (Just ty) rest
caseOneBinder (Generalized ex ty) = Generalized_ ex ty

data BinderInfo = BinderInfo { _biGeneralizability :: !Generalizability
                             , _biExplicitness     :: !Explicitness
                             , _biMaybeName        :: !(Maybe Name)
                             , _biMaybeType        :: !(Maybe Term) }
                 deriving (Eq, Ord, Show, Read)
makeLenses ''BinderInfo

unconsOneBinder :: Binders -> (BinderInfo, [Binder])
unconsOneBinder (b :| bs) =
  case caseOneBinder b of
    Binder_ g ei name ty mb' -> (BinderInfo g ei (Just name) ty, maybeToList mb' ++ bs)
    Generalized_ ei t -> (BinderInfo Generalizable ei Nothing (Just t), bs)

unconsOneBinderFromType :: Term -> Maybe (BinderInfo, Term)
unconsOneBinderFromType (Forall bbs t) = Just $ second (maybeForall ?? t) (unconsOneBinder bbs)
unconsOneBinderFromType (t `Arrow` t') = Just (BinderInfo Ungeneralizable Explicit Nothing (Just t), t')
unconsOneBinderFromType (Parens t)     = unconsOneBinderFromType t
unconsOneBinderFromType _              = Nothing

isComment :: Sentence -> Bool
isComment CommentSentence{} = True
isComment _ = False

normalizeType :: Term -> Term
normalizeType (Parens t)                = normalizeType t
-- We need to normalize the merge of two [App]s becuase there might be a thrid [App]
normalizeType (App (App t args1) args2) = normalizeType $ App t $ args1 <> args2
normalizeType (HasType t _)             = normalizeType t
normalizeType t                         = t

-- | Rewrite all @Coq.*@ references to their Rocq 9 equivalents in the AST.
--
-- Rocq 9 splits the old @Coq.*@ namespace between @Corelib.*@ and @Stdlib.*@.
-- Many former @Coq.X.Y@ modules are now one-line re-exports inside
-- @Stdlib.X.Y@ whose actual content lives at @Corelib.X.Y@. Fully-qualified
-- names do not follow @Require Export@ aliases, so e.g.
-- @Stdlib.Init.Datatypes.app@ does not resolve -- the correct path is
-- @Corelib.Init.Datatypes.app@.
--
-- The set 'corelibShimModules' below lists every @Coq.X.Y@ path whose Stdlib
-- counterpart is a Corelib re-export (derived from the Rocq 9.2 distribution).
-- For those, we rewrite @Coq.@ -> @Corelib.@. Everything else becomes
-- @Stdlib.@.
coqToStdlib :: Data a => a -> a
coqToStdlib = everywhere
  (mkT renameQualid `extT` renameModuleSentence `extT` renameProof `extT` renameSentence)
  where
    renameQualid :: Qualid -> Qualid
    renameQualid (Qualified modId accId)
      -- An exact reference to the moved module puts its name in accId.
      -- Keep accessor components intact, including the special .Z/.N form.
      | modId == "Coq.Program.Wf"
      , "WfExtensionality" `isModulePrefixOf` accId =
          Qualified "Stdlib.Program.WfExtensionality" accId
      | otherwise = Qualified (rocq9RenameModuleReference modId) accId
    renameQualid q = q

    -- ModuleIdent is a type alias for Text, so we can't use mkT on it directly.
    -- Instead we pattern-match on ModuleSentence constructors that contain ModuleIdents.
    renameModuleSentence :: ModuleSentence -> ModuleSentence
    renameModuleSentence (ModuleImport ie mods) =
      ModuleImport ie (fmap rocq9RenameModuleReference mods)
    -- Require targets name library files, not the nested modules they contain.
    -- With From, operands are relative to its prefix, not independent roots.
    renameModuleSentence (Require (Just from) ie mods) =
      Require (Just (rocq9RenameModule from)) ie mods
    renameModuleSentence (Require Nothing ie mods) =
      Require Nothing ie (fmap rocq9RenameModule mods)
    renameModuleSentence (ModuleAssignment m1 m2) =
      ModuleAssignment m1 (rocq9RenameModuleReference m2)

    -- Tactics are raw Text, so rewrite only code-bearing payloads, not all Text.
    renameProof :: Proof -> Proof
    renameProof (ProofQed tactics) = ProofQed (rocq9RewriteText tactics)
    renameProof (ProofDefined tactics) = ProofDefined (rocq9RewriteText tactics)
    renameProof (ProofAdmitted tactics) = ProofAdmitted (rocq9RewriteText tactics)

    renameSentence :: Sentence -> Sentence
    renameSentence (ProgramSentence sentence tactics) =
      ProgramSentence sentence (fmap rocq9RewriteText tactics)
    renameSentence sentence = sentence

-- | Rewrite a single module identifier from the Coq-8.20 @Coq.*@ namespace
-- to its Rocq-9 equivalent (@Corelib.*@ for shim paths, @Stdlib.*@ otherwise).
rocq9RenameModule :: ModuleIdent -> ModuleIdent
rocq9RenameModule m
  | m == "Coq"                           = "Stdlib"
  | Just rest <- T.stripPrefix "Coq." m
  , any (`isModulePrefixOf` rest) corelibShimModules = "Corelib." <> rest
  | Just rest <- T.stripPrefix "Coq." m  = "Stdlib."  <> rest
  | otherwise                            = m

-- | References and Import/assignment targets can name the moved inner module.
-- Its containing library is just Stdlib.Program.WfExtensionality.
rocq9RenameModuleReference :: ModuleIdent -> ModuleIdent
rocq9RenameModuleReference m
  | old `isModulePrefixOf` m = new <> T.drop (T.length old) m
  | otherwise = rocq9RenameModule m
  where
    old = "Coq.Program.Wf.WfExtensionality"
    new = "Stdlib.Program.WfExtensionality.WfExtensionality"

isModulePrefixOf :: ModuleIdent -> ModuleIdent -> Bool
isModulePrefixOf prefix path = prefix == path || (prefix <> ".") `T.isPrefixOf` path

-- | Apply the Rocq-9 @Coq.*@ -> @Corelib.*@/@Stdlib.*@ rewrite to plain text
-- (used for preamble/midamble files and raw proof/obligation tactics).
--
-- Only root @Coq.*@ paths are rewritten: whole identifiers and qualified paths
-- stay together, while symbolic and numeric tokens do not absorb a following
-- root reference. From commands rewrite only their prefix,
-- including bare @Coq@, leaving relative Require operands intact. Bare @Coq@
-- names elsewhere stay unchanged.
-- Comments and quoted string literals are copied verbatim, including nested
-- comments and doubled quote escapes, without recognizing commands inside them.
--
-- Each complete path uses the same renaming as AST module references:
-- @Coq.Program.Wf.WfExtensionality@ moves to
-- @Stdlib.Program.WfExtensionality.WfExtensionality@, Corelib shim paths use
-- @Corelib.@, and other paths use @Stdlib.@. Matching whole module components
-- keeps @Coq.Program.WfExtensionality@ distinct from the @Coq.Program.Wf@ shim.
--
-- The Rocq-9 static preamble loads @Stdlib.Program.WfExtensionality@ once,
-- independently of the spelling of user-supplied Require commands.
rocq9RewriteText :: T.Text -> T.Text
rocq9RewriteText = T.concat . scan False
  where
    -- Within a From Require command, module paths are relative until its final
    -- dot. Consume whole paths so embedded Coq components never become roots.
    scan relative text
      | Just after <- T.stripPrefix "\"" text =
          let (literal, rest) = quoted after
          in ("\"" <> literal) : scan relative rest
      | Just after <- T.stripPrefix "(*" text =
          let (comment, rest) = commented 1 after
          in ("(*" <> comment) : scan relative rest
      | Just (c, _) <- T.uncons text, isDigit c =
          let (number, rest) = numericToken text
          in number : scan relative rest
      | not (T.null path), relative =
          renderPath path separators : scan True afterPath
      | path == "From", Just (prefix, rest) <- fromRequire afterPath =
          path : (prefix ++ scan True rest)
      | not (T.null path) = renderPath (rewritePath path) separators : scan False afterPath
      -- A single dot followed by an identifier is a FIELD token, not a root.
      | Just after <- T.stripPrefix "." text
      , let (field, fieldSeparators, rest) = qualifiedPath after
      , not (T.null field) = ("." <> renderPath field fieldSeparators) : scan relative rest
      | not (T.null symbols) =
          symbols : scan (relative && not ("." `T.isSuffixOf` symbols)) afterSymbols
      | Just (c, rest) <- T.uncons text = T.singleton c : scan relative rest
      | otherwise = []
      where
        (path, separators, afterPath) = qualifiedPath text
        (symbols, afterSymbols) = symbolicToken text

    -- FIELD tokens can follow whitespace or comments, but their dot must be
    -- immediately followed by an identifier start. Look ahead through trivia
    -- without consuming it unless a field follows; command dots and notation
    -- stay outside the path. Match canonical names, retaining each separator.
    qualifiedPath text
      | Just (c, _) <- T.uncons text, isIdentInitial c =
          let (name, rest) = T.span isIdentChar text
              (beforeDot, fieldText) = trivia rest
          in case T.stripPrefix "." fieldText of
            Just after
              | let (suffix, separators, following) = qualifiedPath after
              , not (T.null suffix) ->
                  (name <> "." <> suffix, (beforeDot <> ".") : separators, following)
            _ -> (name, [], rest)
      | otherwise = ("", [], text)

    -- All supported substitutions preserve the number of path components,
    -- including the WfExtensionality move. Copy their original separators.
    renderPath path separators =
      T.concat $ zipWith (<>) ("" : separators) (T.splitOn "." path)

    -- Keep punctuation together, including trailing dots and leading pattern
    -- apostrophes. Comments and strings start separate lexical regions.
    symbolicToken text =
      let (symbols, _) = T.span (\c -> not (isIdentInitial c || isDigit c || isSpace c || c == '"')) text
          (beforeComment, _) = T.breakOn "(*" symbols
      in T.splitAt (T.length beforeComment) text

    -- Follow Rocq's NumTok.Unsigned grammar, preserving the original spelling.
    -- Hex digits can absorb C: 0x1Coq is a numeral followed by oq, not Coq.
    numericToken text
      | Just ('0', rest) <- T.uncons text
      , Just (base, digits) <- T.uncons rest, base == 'x' || base == 'X'
      , Just (c, _) <- T.uncons digits, isHexDigit c =
          first (("0" <> T.singleton base) <>) (numberParts isHexDigit "pP" digits)
      | otherwise = numberParts isDigit "eE" text

    numberParts digit exponents text =
      let digitOrUnderscore c = digit c || c == '_'
          (integer, afterInteger) = T.span digitOrUnderscore text
          (fraction, afterFraction)
            | Just ('.', digits) <- T.uncons afterInteger
            , Just (c, _) <- T.uncons digits, digitOrUnderscore c =
                first ("." <>) (T.span digitOrUnderscore digits)
            | otherwise = ("", afterInteger)
          (exponent, afterExponent)
            | Just (e, rest) <- T.uncons afterFraction, e `T.elem` exponents
            , let (sign, digits) = case T.uncons rest of
                    Just (s, following) | s == '+' || s == '-' -> (T.singleton s, following)
                    _ -> ("", rest)
            , Just (c, _) <- T.uncons digits, isDigit c =
                first ((T.singleton e <> sign) <>)
                  (T.span (\d -> isDigit d || d == '_') digits)
            | otherwise = ("", afterFraction)
      in (integer <> fraction <> exponent, afterExponent)

    -- Recognize just From <prefix> Require, allowing comments between tokens.
    -- This is not a vernacular parser; Import/Export and operands need only be
    -- copied until the command ends. Only this prefix may rename bare Coq.
    fromRequire text
      | not (T.null beforePrefix), not (T.null prefix)
      , not (T.null beforeRequire)
      , Just rest <- T.stripPrefix "Require" requireText
      , maybe True (not . isPathChar . fst) (T.uncons rest) =
          Just ([beforePrefix, renderPath (rocq9RenameModuleReference prefix) separators,
                 beforeRequire, "Require"], rest)
      | otherwise = Nothing
      where
        (beforePrefix, prefixText) = trivia text
        (prefix, separators, afterPrefix) = qualifiedPath prefixText
        (beforeRequire, requireText) = trivia afterPrefix

    trivia text =
      let (space, rest) = T.span (\c -> isSpace c && not (isPathChar c)) text
      in case T.stripPrefix "(*" rest of
        Just after ->
          let (comment, following) = commented 1 after
              (more, remaining) = trivia following
          in (space <> "(*" <> comment <> more, remaining)
        Nothing -> (space, rest)

    -- Rocq escapes a quote inside a string by doubling it.
    quoted text
      | T.null rest = (pre, "")
      | Just after <- T.stripPrefix "\"\"" rest =
          first ((pre <> "\"\"") <>) (quoted after)
      | otherwise = (pre <> "\"", T.drop 1 rest)
      where
        (pre, rest) = T.breakOn "\"" text

    -- Quotes inside a comment can themselves contain comment delimiters.
    commented :: Int -> T.Text -> (T.Text, T.Text)
    commented depth text
      | Just after <- T.stripPrefix "(*" text =
          first ("(*" <>) (commented (depth + 1) after)
      | Just after <- T.stripPrefix "*)" text =
          if depth == 1 then ("*)", after)
          else first ("*)" <>) (commented (depth - 1) after)
      | Just after <- T.stripPrefix "\"" text =
          let (literal, rest) = quoted after
          in first (("\"" <> literal) <>) (commented depth rest)
      | not (T.null pre) = first (pre <>) (commented depth rest)
      | Just (c, after) <- T.uncons text = first (T.cons c) (commented depth after)
      | otherwise = ("", "")
      where
        (pre, rest) = T.break (`elem` ("(*\"" :: String)) text

    rewritePath path
      | "Coq." `T.isPrefixOf` path, path /= "Coq." = rocq9RenameModuleReference path
      | otherwise = path

    -- Rocq's Unicode.is_valid_ident_initial accepts Letter and IdentSep.
    -- Numbers and non-spacing marks can continue, but cannot start identifiers.
    isIdentInitial c = isLetter c || c == '_' || c == '\xa0'

    isPathChar c = isIdentChar c || c == '.'

    -- Continuation characters for whole identifiers.
    -- Rocq 9.0.1 clib/unicode.ml includes non-spacing marks in IdentPart
    -- and U+00A0 in IdentSep.
    -- Superscript decimal digits are symbols in both Coq 8.20.1 and Rocq 9.0.1.
    -- https://github.com/rocq-prover/rocq/blob/V9.0.1/clib/unicode.ml
    isIdentChar c
      | c `elem` ("\xb2\xb3\xb9\x2070\x2074\x2075\x2076\x2077\x2078\x2079" :: String) = False
      | otherwise = isAlphaNum c || generalCategory c == NonSpacingMark
                 || c == '_' || c == '\'' || c == '\xa0'

-- | The Rocq-version-aware text rewriter used by the driver for user-supplied
-- preamble/midamble files. The Coq-8.20 target leaves text untouched (so the
-- default output is byte-identical to the pre-Rocq-9 tool); the Rocq-9 target
-- applies 'rocq9RewriteText'.
rewriteTextFor :: RocqVersion -> T.Text -> T.Text
rewriteTextFor Rocq_9_0  = rocq9RewriteText
rewriteTextFor Rocq_8_20 = id

-- | The Rocq-version-aware AST rewriter used by the driver for generated
-- declarations. The Coq-8.20 target is the identity; the Rocq-9 target applies
-- 'coqToStdlib'.
rewriteASTFor :: Data a => RocqVersion -> a -> a
rewriteASTFor Rocq_9_0  = coqToStdlib
rewriteASTFor Rocq_8_20 = id

-- | @Coq.X.Y@ paths whose Stdlib counterpart is a one-line Corelib re-export
-- in Rocq 9. Fully-qualified names beneath these paths must use @Corelib.@
-- rather than @Stdlib.@.
--
-- Derived from the Rocq 9.2 distribution. The Corelib\/Stdlib split is stable
-- across the Rocq 9.x series, and this list is verified against 9.0 by the
-- @test-rocq9@ and @test-rocq9-translation@ CI jobs.
corelibShimModules :: Set T.Text
corelibShimModules = Set.fromList
  [ "Array.ArrayAxioms", "Array.PrimArray"
  , "BinNums.IntDef", "BinNums.NatDef", "BinNums.PosDef"
  , "Classes.CMorphisms", "Classes.CRelationClasses", "Classes.Equivalence"
  , "Classes.Init", "Classes.Morphisms", "Classes.Morphisms_Prop"
  , "Classes.RelationClasses", "Classes.SetoidTactics"
  , "Compat.Coq818", "Compat.Coq819", "Compat.Coq820"
  , "Floats.FloatAxioms", "Floats.FloatClass", "Floats.FloatOps"
  , "Floats.PrimFloat", "Floats.SpecFloat"
  , "Init.Byte", "Init.Datatypes", "Init.Decimal", "Init.Hexadecimal"
  , "Init.Logic", "Init.Ltac", "Init.Nat", "Init.Notations", "Init.Number"
  , "Init.Peano", "Init.Prelude", "Init.Specif", "Init.Sumbool"
  , "Init.Tactics", "Init.Tauto", "Init.Wf"
  , "Lists.ListDef"
  , "Numbers.BinNums"
  , "Numbers.Cyclic.Int63.CarryType"
  , "Numbers.Cyclic.Int63.PrimInt63"
  , "Numbers.Cyclic.Int63.Sint63Axioms"
  , "Numbers.Cyclic.Int63.Uint63Axioms"
  , "Program.Basics", "Program.Tactics", "Program.Utils", "Program.Wf"
  , "Relations.Relation_Definitions"
  , "Setoids.Setoid"
  , "Strings.PrimString", "Strings.PrimStringAxioms"
  , "derive.Derive"
  , "extraction.ExtrHaskellBasic", "extraction.ExtrOcamlBasic", "extraction.Extraction"
  , "ssr.ssrbool", "ssr.ssrclasses", "ssr.ssreflect", "ssr.ssrfun"
  , "ssr.ssrsetoid", "ssr.ssrunder"
  , "ssrmatching.ssrmatching"
  ]
