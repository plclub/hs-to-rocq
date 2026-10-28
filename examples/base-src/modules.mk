# Shared module lists for examples/base-src and examples/rocq9.0/base-src.
# Caller must set OUT (output directory) before including this file.

# Handwritten modules (usually by modification of generated version)
HANDMOD = \
  HsToRocq/Wf \
  HsToRocq/Skip \
  HsToRocq/DeferredFix \
  HsToRocq/DeferredFixImpl \
  HsToRocq/Unpeel \
  GHC/Num \
  GHC/Char \
  GHC/Real \
  GHC/Enum \
  Data/Bits \
  Data/Functor/Classes \
  GHC/Prim \
  GHC/Types \
  GHC/Tuple \
  Data/Type/Equality \
  HsToRocq/Err \
  GHC/Err \
  HsToRocq/Nat \
  GHC/Unicode \
  Prelude\

# Generated modules that must be listed early in _CoqProject
# (before other generated modules) to avoid Coq stack overflow
# in typeclass resolution.
EARLY_GHC_INTERNAL_MODULES = \
  Data/Functor/Identity \
  Data/Traversable

# No early base modules currently needed
EARLY_BASE_MODULES =

# Generated modules from ghc-internal
GHC_INTERNAL_MODULES = \
  Data/Maybe \
  Data/List \
  Data/OldList \
  Data/Bool \
  Data/Tuple \
  Data/Void \
  Data/Function \
  Data/Ord \
  Data/Functor \
  Data/Either \
  Data/Proxy \
  Control/Monad \
  Data/Monoid \
  Data/Functor/Utils \
  Control/Monad/Fail \
  Data/Foldable \
  Data/Functor/Const \
  Control/Category \
  Control/Arrow

# GHC/* modules in ghc-internal that need special path mapping
GHC_INTERNAL_GHC_MODULES = \
  GHC/List

# Generated modules still in base/src (with real content, not re-exports)
BASE_MODULES = \
  Control/Applicative \
  Data/Bifunctor \
  Data/List/NonEmpty \
  Data/Semigroup \
  Data/Functor/Compose \
  Data/Functor/Product \
  Data/Functor/Sum \
  Data/Bifoldable \
  Data/Bitraversable \
  Control/Monad/Zip

MODULES = $(GHC_INTERNAL_MODULES) $(GHC_INTERNAL_GHC_MODULES) $(BASE_MODULES)
EARLY_MODULES = $(EARLY_GHC_INTERNAL_MODULES) $(EARLY_BASE_MODULES)
ALL_MODULES = $(EARLY_MODULES) $(MODULES)

RENAMED = \
  Data/SemigroupInternal \

# generated from drop-in/
DROPIN =

# also generated from drop-in/
SPECIAL_MODULES = \
  GHC/Base

VFILES_GHC_INTERNAL     = $(addprefix $(OUT)/,$(addsuffix .v,$(GHC_INTERNAL_MODULES)))
VFILES_GHC_INTERNAL_GHC = $(addprefix $(OUT)/,$(addsuffix .v,$(GHC_INTERNAL_GHC_MODULES)))
VFILES_BASE_GEN         = $(addprefix $(OUT)/,$(addsuffix .v,$(BASE_MODULES)))
VFILES_EARLY_GHC_INTERNAL = $(addprefix $(OUT)/,$(addsuffix .v,$(EARLY_GHC_INTERNAL_MODULES)))
VFILES_EARLY_BASE       = $(addprefix $(OUT)/,$(addsuffix .v,$(EARLY_BASE_MODULES)))
VFILES_GEN       = $(VFILES_GHC_INTERNAL) $(VFILES_GHC_INTERNAL_GHC) $(VFILES_BASE_GEN) $(VFILES_EARLY_GHC_INTERNAL) $(VFILES_EARLY_BASE)
VFILES_RENAMED   = $(addprefix $(OUT)/,$(addsuffix .v,$(RENAMED)))
VFILES_MAN       = $(addprefix $(OUT)/,$(addsuffix .v,$(HANDMOD)))
VFILES_SPECIAL   = $(addprefix $(OUT)/,$(addsuffix .v,$(SPECIAL_MODULES)))
VFILES_DROPIN    = $(addprefix $(OUT)/,$(addsuffix .v,$(DROPIN)))

VFILES   = $(VFILES_MAN) $(VFILES_GEN) $(VFILES_SPECIAL) $(VFILES_DROPIN) $(VFILES_RENAMED)
