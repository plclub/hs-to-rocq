{-# LANGUAGE CPP, LambdaCase, OverloadedStrings, PatternSynonyms, RecordWildCards #-}

-- Source equations for a fold over nested datatypes sometimes expose
-- structural recursion only after specializing its rank-2 algebra. Keep the
-- same public type and equations; the ordinary kernel guard check still
-- checks both local fixpoints.
module HsToRocq.ConvertHaskell.NestedFold (nestedFold, freshenFoldValues) where

#include "ghc-compat.h"

import Control.Applicative ((<|>))
import Control.Monad (foldM, guard)
import Data.Foldable (toList)
import Data.Generics (Data, everywhere, everything, extQ, mkQ, mkT)
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified GHC
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Types.Name as G
import qualified GHC.Types.Name.Occurrence as G
#else
import qualified Name as G
import qualified OccName as G
#endif
import HsToRocq.ConvertHaskell.Definitions
import HsToRocq.Rocq.FreeVars (getFreeVars)
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Util (appList, qualidBase, pattern App1, pattern LetFix)

spine :: Term -> (Term, [Arg])
spine (App h xs) = let (f, as) = spine h in (f, as ++ toList xs)
spine (Parens t) = spine t
spine t = (t, [])

-- Reject possible capture conservatively: count every occurrence (including
-- patterns, binders, let names and explicit applications), not just free vars.
count :: Data a => Qualid -> a -> Int
count n = everything (+) (0 `mkQ` (\q -> fromEnum (q == n)))

onlyReferences :: Data a => Qualid -> a -> Bool
onlyReferences n x = count n x == everything (+) (0 `mkQ` refs) x
  where refs (Qualid q) = fromEnum (q == n)
        refs (ExplicitApp q _) = fromEnum (q == n)
        refs _ = 0

variable :: Term -> Maybe Qualid
variable (Qualid q) = Just q
variable (ExplicitApp q []) = Just q
variable _ = Nothing

fresh :: Data a => a -> Qualid
fresh x = go (0 :: Int)
  where go i = let n = "fold_" <> T.pack (show i) <> "__"
               in if everything (&&) (True `mkQ` ((/= n) . qualidBase)) x
                  then Bare n else go (i+1)

rewrite :: (Term -> Term) -> Term -> Term
rewrite f = everywhere (mkT f)

renameRefs :: Qualid -> Qualid -> Term -> Term
renameRefs from to = rewrite $ \case
  Qualid q | q == from -> Qualid to
  ExplicitApp q as | q == from -> ExplicitApp to as
  e -> e

-- A Gallina identifier no longer tells us whether a Haskell occurrence of
-- "p" names a value or a type. Freshen at the renamed source, where even two
-- nested value binders spelled "p" have distinct GHC Names. tidyNameOcc
-- changes the spelling but retains the Unique used for GHC type lookups.
freshenFoldValues :: Data matches => ConvertedDefinition -> matches -> Maybe (matches, Term -> Term)
freshenFoldValues ConvertedDefinition{..} source = do
  Qualified{} <- pure _convDefName
  Fun _ (Let h params _ (Fun _ inner) call) <- pure _convDefBody
  (_, [PosArg handler, PosArg _]) <- pure (spine call)
  guard (variable handler == Just h && _convDefName `elem` getFreeVars inner)
  let protected = S.fromList [n | b <- _convDefArgs ++ params, Ident (Bare n) <- names b]
      names (Typed _ Implicit ns _) = toList ns
      names (ImplicitBinders ns) = toList ns
      names _ = []
      sourceNames = everything (++) ([] `mkQ` (\n -> [n :: G.Name])) source
      spelling = T.pack . G.occNameString . G.nameOccName
      reserved = S.fromList (map spelling sourceNames ++
          everything (++) ([] `mkQ` (\q -> [qualidBase q])) (_convDefArgs, _convDefBody, _convDefType))
      available = [s | i <- [0 :: Integer ..], let s = "value_" <> T.pack (show i) <> "__",
                       s `S.notMember` reserved]
      allocate (next@(s:ss), m) n
        | G.isInternalName n && G.isVarOcc (G.nameOccName n)
        , spelling n `S.member` protected && M.notMember n m =
            (ss, M.insert n (G.tidyNameOcc n (G.mkVarOcc (T.unpack s))) m)
        | otherwise = (next, m)
      allocate acc _ = acc
      -- Do not rename a free internal Name just because it shares a spelling
      -- with a type parameter. Collect actual binders here, and rewrite all
      -- occurrences of those same Names (including local signatures) below.
      patternName :: GHC.Pat GHC.GhcRn -> [G.Name]
      patternName (GHC.VarPat NOEXTP (GHC.L _ n)) = [n]
      patternName (GHC.AsPat NOEXTP (GHC.L _ n) _) = [n]
      patternName _ = []
      valueName :: GHC.HsBind GHC.GhcRn -> [G.Name]
      valueName GHC.FunBind{GHC.fun_id = GHC.L _ n} = [n]
      valueName _ = []
      bound = everything (++) ([] `mkQ` patternName `extQ` valueName) source
      replacements = snd (foldl' allocate (available, M.empty) bound)
  guard (not (M.null replacements))
  let restore = M.fromList [(Bare (spelling n'), Bare (spelling n))
                           | (n,n') <- M.toList replacements]
  pure (everywhere (mkT (\n -> M.findWithDefault n n replacements)) source,
        everywhere (mkT (\q -> M.findWithDefault q q restore)))

nestedFold :: ConvertedDefinition -> Maybe ConvertedDefinition
nestedFold cd@ConvertedDefinition{..} = do
  ty <- _convDefType
  Fun bs body <- pure _convDefBody
  -- Local recursive definitions with the same short name as a bound
  -- variable require scope-aware rewriting. Restrict this pass to globals.
  Qualified{} <- pure _convDefName
  result <- (Fun bs <$> capture ty bs body) <|> rotate ty bs body
  guard (count _convDefName result == 0)
  pure cd{_convDefBody = result}
 where
  -- f h t = case (h,t) of ... f h child ...
  --   ==> let fix go {index} t := case t of ... go child ... in go t
  capture (Arrow handlerType@Forall{} (Arrow treeType result)) bs body = do
    [ExplicitBinder (Ident h), ExplicitBinder (Ident t)] <- pure (toList bs)
    (_, [PosArg signature, PosArg (Qualid index)]) <- pure (spine treeType)
    Forall _ (Arrow input _) <- pure handlerType
    (signature', [PosArg _]) <- pure (spine input)
    guard (signature == signature')
    guard (count index handlerType == 0)
    let loop = fresh (_convDefBody, _convDefType, _convDefArgs)
    indexBinder <- dynamicIndex index
    guard (index /= h && index /= t)
    Match (MatchItem hterm Nothing Nothing :| [m@(MatchItem (Qualid t') Nothing Nothing)]) Nothing eqs <- pure body
    h' <- variable hterm
    guard (h == h' && t == t')
    let clause (Equation (MultPattern (hp :| [tp]) :| []) rhs) = do
          guard (count h tp == 0 && onlyReferences h rhs)
          rhs' <- case hp of
            UnderscorePat -> pure rhs
            QualidPat alias@Bare{} -> do
              guard (count alias tp == 0 && onlyReferences alias rhs)
              pure (renameRefs alias h rhs)
            _ -> Nothing
          let step e = case spine e of
                (Qualid f, PosArg fixed : rest)
                  | f == _convDefName && variable fixed == Just h -> appList (Qualid loop) rest
                _ -> e
          pure (Equation (MultPattern (tp :| []) :| []) (rewrite step rhs'))
        clause _ = Nothing
    clauses <- traverse clause eqs
    -- Only the rank-2 handler is known to be passed unchanged. Leave class
    -- arguments on recursive calls, where their evidence is inferred.
    let dictionaries = [b | b@Generalized{} <- _convDefArgs]
        treeBinder = Typed Ungeneralizable Explicit (Ident t :| []) treeType
        go = FixBody loop (indexBinder :| (dictionaries ++ [treeBinder]))
                     (Just (StructOrder t)) (Just result) (Match (m :| []) Nothing clauses)
    pure (LetFix go (App1 (Qualid loop) (Qualid t)))
  capture _ _ _ = Nothing

  -- f t p... = let h x = ... f child p... in fold h t
  --   ==> let fix h x := ... fold h child in fold h t
  rotate (Arrow treeTy restTy) bs (Let h params (Just hty) (Fun hargs hbody) ret) = do
    (index, typeParams) <- unconsImplicit params
    [ExplicitBinder (Ident x)] <- pure (toList hargs)
    Arrow xType result <- pure hty
    (Qualid alg@Qualified{}, [PosArg hterm, PosArg (Qualid t)]) <- pure (spine ret)
    h' <- variable hterm
    guard (h == h' && h /= x && h /= index)
    ExplicitBinder (Ident root) : ps <- pure (toList bs)
    guard (root == t)
    fixed <- traverse (\case ExplicitBinder (Ident n) -> Just n; _ -> Nothing) ps
    -- A constrained wrapper could receive different implicit evidence on a
    -- recursive call, even when the explicit value arguments agree.
    guard (all (\case Generalized{} -> False; _ -> True) _convDefArgs)
    PosArg (Qualid a) : _ <- pure (reverse (snd (spine treeTy)))
    ab <- dynamicIndex a
    -- Re-entering the wrapper at a different tree index must not change
    -- either the types of its saved arguments or the handler's environment.
    resultTy <- foldM (\ty _ -> case ty of
                          Arrow s r | count a s == 0 -> Just r
                          _ -> Nothing) restTy fixed
    guard (a == index || (a `notElem` getFreeVars hbody && count a hty == 0))
    guard (count h hbody == 0 && all (`onlyReferences` hbody) fixed)
    guard (all (`notElem` [x,index,h]) fixed && count t hbody == 0)
    guard (all (\n -> count n hty == 0) (root:fixed))
    -- Resolve the fold's implicit dictionaries in the original wrapper
    -- context. Inserting a fresh reference to it under a constructor pattern
    -- could instead select evidence brought into scope by that constructor.
    let used = (_convDefBody, _convDefArgs, _convDefType)
        run = fresh used
        algebra = fresh (used,run)
        algebraType = Forall typeParams hty
        algBinder = Typed Ungeneralizable Explicit (Ident algebra :| []) algebraType
        savedFold = Let run [ab,algBinder] (Just (Arrow treeTy resultTy))
                        (App1 (Qualid alg) (ExplicitApp algebra []))
        applyFold = App1 (Qualid run) (ExplicitApp h [])
        step e = case spine e of
          (Qualid f, PosArg child : rest)
            | f == _convDefName && rest == map (PosArg . Qualid) fixed -> App1 applyFold child
          _ -> e
        hb = Typed Ungeneralizable Explicit (Ident x :| []) xType
        go = FixBody h (typeParams <> (hb :| [])) (Just (StructOrder x))
                     (Just result) (rewrite step hbody)
        wrapper = Fun bs (LetFix go (App1 applyFold (Qualid root)))
    pure (savedFold wrapper)
  rotate _ _ _ = Nothing

  dynamicIndex index = do
    [b] <- pure [Typed g Implicit (Ident index :| []) kind
                | Typed g Implicit names kind <- _convDefArgs, Ident index `elem` names]
    -- In particular, no captured dictionary can depend on the varying index.
    guard (count index _convDefArgs == 1)
    pure b

  unconsImplicit [b@(ImplicitBinders (Ident n :| []))] = Just (n, b :| [])
  unconsImplicit [b@(Typed _ Implicit (Ident n :| []) _)] = Just (n, b :| [])
  unconsImplicit _ = Nothing
