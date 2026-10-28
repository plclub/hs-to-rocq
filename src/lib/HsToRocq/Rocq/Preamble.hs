{-|
Module      : HsToRocq.Rocq.Preamble
Description : Static preamble for all hs-to-rocq output
Copyright   : Copyright © 2017 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}

module HsToRocq.Rocq.Preamble
    ( staticPreamble
    , builtInAxioms
    ) where

import Data.Text (Text)
import qualified Data.Text as T
import HsToRocq.Rocq.Gallina
import HsToRocq.Rocq.Gallina.Orphans ()
import qualified Data.Map as M
import Data.Bifunctor

staticPreamble :: RocqVersion -> Text
staticPreamble version = T.unlines $
 [ "(* Default settings (from HsToRocq.Rocq.Preamble) *)"
 , ""
 , "Generalizable All Variables."
 , ""
 , "Unset Implicit Arguments."
 , "Set Maximal Implicit Insertion."
 , "Unset Strict Implicit."
 , "Unset Printing Implicit Defensive."
 , ""
 , "Require " <> stdlibPrefix version <> "Program.Tactics."
 , "Require " <> stdlibPrefix version <> "Program.Wf."
 ] ++ case version of
    Rocq_8_20 -> []
    Rocq_9_0  -> ["Require Import Stdlib.Program.WfExtensionality."]
  where
    stdlibPrefix Rocq_8_20 = "Coq."
    stdlibPrefix Rocq_9_0  = "Stdlib."

-- | When a free variable of this name appears in the output,
-- an axiom of the type given here is added to the preamble
builtInAxioms :: M.Map Qualid Term
builtInAxioms = M.fromList
    [ first Bare
      ("missingValue"   =: Forall [ ImplicitBinders (pure (Ident (Bare "a"))) ] a)
    ]
  where
   a = "a"
   (=:) = (,)
   infix 0 =:
