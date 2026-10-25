include ../../common.mk

OUT=../../base

# Not all of these need to be handwritten. Eventually we should be able to
# generate some of these modules as hs-to-rocq is improved.
# see [notes.md] for discussion of issues

include modules.mk

all:  vfiles coq base-thy

filelist:
	@ls -1 $(addprefix base/src/,$(addsuffix .hs,$(BASE_MODULES)))
	@ls -1 $(addprefix ghc-internal/src/GHC/Internal/,$(addsuffix .hs,$(GHC_INTERNAL_MODULES)))

vfiles: $(OUT)/edits $(OUT)/README.md $(OUT)/_CoqProject $(OUT)/coq-hs-to-rocq-base.opam $(VFILES)

$(OUT)/_CoqProject : Makefile modules.mk
	mkdir -p $(OUT)
	> $@
	echo '-Q . ""' >> $@
	echo $(addsuffix .v,$(HANDMOD)) $(addsuffix .v,$(EARLY_MODULES)) >> $@
	echo $(addsuffix .v,$(MODULES)) >> $@
	echo $(addsuffix .v,$(RENAMED)) >> $@
	echo $(addsuffix .v,$(SPECIAL_MODULES)) >> $@
	echo $(addsuffix .v,$(DROPIN)) >> $@

$(OUT)/Makefile: $(OUT)/_CoqProject
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile

$(OUT)/coq-hs-to-rocq-base.opam : Makefile
	mkdir -p $(OUT)
	> $@
	echo 'opam-version: "2.0"' >> $@
	echo 'name: "coq-hs-to-rocq-base"' >> $@
	echo 'version: "dev"' >> $@
	echo 'synopsis: "Coq translation of parts of the Haskell base library"' >> $@
	echo 'maintainer: "antal.b.sz@gmail.com"' >> $@
	echo 'authors: [' >> $@
	echo '  "Antal Spector-Zabusky"' >> $@
	echo '  "Joachim Breitner"' >> $@
	echo '  "Yao Li"' >> $@
	echo '  "Christine Rizkallah"' >> $@
	echo '  "John Wiegley"' >> $@
	echo '  "Stephanie Weirich"' >> $@
	echo ']' >> $@
	echo 'license: "MIT"' >> $@
	echo 'homepage: "https://github.com/plclub/hs-to-rocq"' >> $@
	echo 'bug-reports: "https://github.com/plclub/hs-to-rocq/issues"' >> $@
	echo 'dev-repo: "git+https://github.com/plclub/hs-to-rocq.git"' >> $@
	echo 'depends: [' >> $@
	echo '  "coq" {>= "8.20" & < "8.21~"}' >> $@
	echo ']' >> $@
	echo 'build: [' >> $@
	echo '  ["coq_makefile" "-f" "_CoqProject" "-o" "Makefile"]' >> $@
	echo '  [make "-j%{jobs}%"]' >> $@
	echo ']' >> $@
	echo 'install: [' >> $@
	echo '  [make "install"]' >> $@
	echo ']' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../examples/base-src/edits $(OUT)/edits

$(OUT)/README.md:
	mkdir -p $(OUT)
	> $@
	echo 'This directory contains a Coq'\''ified version of the Haskell base library' >> $@
	echo 'Do not edit files here! Instead, look in `examples/base-src`.' >> $@

coq: $(OUT)/Makefile $(VFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

BASE_THY=../../base-thy

base-thy: coq
	cd $(BASE_THY) && coq_makefile -f _CoqProject -o Makefile && $(MAKE) -f Makefile

# Common options shared by all translation rules
# NOTE: -i gen-files is NOT included here because it would cause GHC to
# find our stub modules instead of the installed ghc-internal package.
# Only GHC/Base needs -i gen-files (see HS_TO_ROCQ_OPTS_GHC_BASE).
HS_TO_ROCQ_OPTS_COMMON := \
    -e edits \
    -N \
    -I gen-files \
    -I ghc-internal/include \
    --iface-dir $(OUT) \
    --dependency-dir deps \
    -o $(OUT)

# Options for ghc-internal modules
# Use a dummy unit-id so GHC resolves GHC.Internal.* imports from
# the installed ghc-internal package (not our gen-files stubs).
HS_TO_ROCQ_OPTS_INTERNAL := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    --ghc -this-unit-id --ghc ghc-internal-local

# For GHC/Base we use -this-unit-id ghc-internal without hiding the
# installed package. GHC treats our source as part of ghc-internal,
# so SOURCE imports work and desugaring uses our local class definitions.
# gen-files stubs shadow modules with boot-file conflicts.
HS_TO_ROCQ_OPTS_GHC_BASE := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    -i gen-files \
    -i ghc-internal/src \
    --ghc -this-unit-id --ghc ghc-internal

# Options for base/src modules
HS_TO_ROCQ_OPTS_BASE := \
    $(HS_TO_ROCQ_OPTS_COMMON) \
    -i base/src \
    --ghc -this-unit-id --ghc base


include deps/*.mk

.SECONDEXPANSION:

# Rule for Data/* and Control/* modules from ghc-internal
# Source: ghc-internal/src/GHC/Internal/$*.hs
$(VFILES_GHC_INTERNAL) $(VFILES_EARLY_GHC_INTERNAL): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     ghc-internal/src/GHC/Internal/$*.hs
	test -e $@

# Rule for GHC/* modules from ghc-internal
# GHC/List -> ghc-internal/src/GHC/Internal/List.hs
$(VFILES_GHC_INTERNAL_GHC): $(OUT)/GHC/%.v : $$(wildcard module-edits/GHC/$$*/preamble.v) $$(wildcard module-edits/GHC/$$*/midamble.v)  $$(wildcard module-edits/GHC/$$*/edits) edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard module-edits/GHC/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/GHC/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/GHC/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     ghc-internal/src/GHC/Internal/$*.hs
	test -e $@

# Rule for modules still in base/src
$(VFILES_BASE_GEN) $(VFILES_EARLY_BASE): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_BASE) \
		     base/src/$*.hs
	test -e $@

# This is renamed, which confuses Make, so hence the special rule
# Data/Semigroup/Internal is in ghc-internal
$(OUT)/Data/SemigroupInternal.v : $(wildcard module-edits/Data/Semigroup/Internal/preamble.v) $(wildcard module-edits/Data/Semigroup/Internal/midamble.v)  $(wildcard module-edits/Data/Semigroup/Internal/edits) edits
	$(HS_TO_ROCQ) $(addprefix -e , $(wildcard module-edits/Data/Semigroup/Internal/edits)) \
	             $(addprefix -p , $(wildcard module-edits/Data/Semigroup/Internal/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/Data/Semigroup/Internal/midamble.v)) \
		     $(HS_TO_ROCQ_OPTS_INTERNAL) \
		     ghc-internal/src/GHC/Internal/Data/Semigroup/Internal.hs
	test -e $(OUT)/Data/SemigroupInternal.v

# We merge GHC.Maybe into GHC.Base, which requires a special rule.
# Both are now in ghc-internal

GHC_BASE_PRE = $(wildcard module-edits/GHC/Base/preamble.v module-edits/GHC/Maybe/preamble.v)
GHC_BASE_MID = $(wildcard module-edits/GHC/Base/midamble.v module-edits/GHC/Maybe/midamble.v)
GHC_BASE_EDITS = $(wildcard module-edits/GHC/Base/edits module-edits/GHC/Maybe/edits)

$(OUT)/GHC/Base.v: $(GHC_BASE_PRE) $(GHC_BASE_MID) $(GHC_BASE_EDITS) edits
	cat /dev/null $(GHC_BASE_PRE) > Base_preamble.v
	cat /dev/null $(GHC_BASE_MID) > Base_midamble.v
	$(HS_TO_ROCQ) -p Base_preamble.v \
	             --midamble Base_midamble.v \
	             $(addprefix -e , $(GHC_BASE_EDITS)) \
	             $(HS_TO_ROCQ_OPTS_GHC_BASE) \
	             ghc-internal/src/GHC/Internal/Stack/Types.hs \
	             gen-files/GHC/Internal/Exception/Context.hs \
	             ghc-internal/src/GHC/Internal/Base.hs ghc-internal/src/GHC/Internal/Maybe.hs
	test -e $(OUT)/GHC/Base.v
	rm -f Base_preamble.v Base_midamble.v

$(VFILES_MAN): $(OUT)/% : manual/%
	rm -f $@
	lndir ../examples/base-src/manual $(OUT)/

$(VFILES_DROPIN): $(OUT)/%.v : module-edits/%/edits edits module-edits/%/preamble.v drop-in/%.hs
	$(HS_TO_ROCQ) -e module-edits/$*/edits \
	             -e edits \
		     $(HS_TO_ROCQ_OPTS_BASE) \
		     drop-in/$*.hs

# Every rule that builds a .v also produces the corresponding interface file
%.h2ci: %.v
	test -e $@

clean:
	rm -rf $(OUT)
	rm -f counts.pdf *.aux *.log

todo:
	-grep -a Parameter $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a Axiom $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a Admitted $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v
	-grep -a errorWithout $(OUT)/*.v $(OUT)/*/*.v $(OUT)/*/*/*.v


counts.pdf: counts.fig
	pdflatex counts

counts.fig: Makefile $(VFILES)
	(echo "\\begin{tabular}{lllll}"; \
    echo "Module & Defs & Class & Insts & Skipped\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Generated modules}}\\\\"; \
	 for i in  $(MODULES) $(DROPIN) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ; echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v | wc -l;  echo "&"; \
           grep -a "skip" module-edits/$$i/edits | wc -l;  echo "\\\\" ) done; \
    echo "\\\\"; \
    echo "\\multicolumn{4}{l}{\emph{Manually adapted modules}}\\\\"; \
	 for i in  $(HANDMOD) ; \
       do (echo $$i; echo "&"; grep -a "Definition" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Class" $(OUT)/$$i.v | wc -l ;  echo "&"; \
           grep -a "Instance" $(OUT)/$$i.v| wc -l; echo "\\\\" ) done; \
	 echo "\\end{tabular}") > counts.fig
