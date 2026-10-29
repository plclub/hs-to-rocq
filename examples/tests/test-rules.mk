# Shared test-suite rules for Coq 8.20 and Rocq 9.0.
#
# Caller must set before including:
#   COMPILER   - compiler binary (default: coqc; use "rocq c" for Rocq 9)
#   SRC_DIR    - source directory for .hs fixtures (default: .)
#   HS_EXTRA   - extra hs-to-rocq flags (default: empty; --target-version 9.0)
#   HS_IMPORT  - extra GHC import-path flags (default: empty; -i $(SRC_DIR))

COMPILER  ?= coqc
SRC_DIR   ?= .
HS_EXTRA  ?=
HS_IMPORT ?=

# typecheck *quietly*
TYPECHECK = $(COMPILER) 1>/dev/null

# tests that should pass
PASS = \
  Simple \
  Self \
  Poly \
  Irrefutable \
  LocalTopoSort \
  InstCtx \
  ExhaustGuard \
  PartialAppliedPolyDataCon \
  NonStructuralRec \
  DotName \
  MapAccumR \
  Sub \
  FTP \
  AddAndReplace \
  FTPDefault \
  PolyInstance2 \
  PolyInstance3 \
  Bits \
  BitsRewrite \
  PatternGuard \
  SoleCtorGuard \
  Guard2 \
  Notations \
  Renamed \
  RenameModule \
  Mutrec \
  GADT \
  Underscore_Module \
  LetPattern \
  AxiomatizeModule \
  RedefineAddAxiom \
  AddTheorem \
  Existential \
  SkipConstructor \
  SkipMatches \
  Promote \
  Promote2 \
  ExceptIn \
  ParserTests \
  StrictPair \
  InstVar \
  PolyKind \
  PolyKindClass \
  ClassKinds \
  UniversePolymorphic \
  Equations \
  TypeAnnotations \
  RocqNestedCorelib \
  RocqMovedAst \
  RocqMovedText \
  RocqQuotedText \
  RocqWfInnerImport \
  RocqFromImports \

# tests that *should* pass but currently fail
TODO_PASS = \
  MutrecInst \
  TopBind \
  ExceptInDataDefinition \

# tests that *should* pass but currently don't even translate
TODO_TRANSLATE = \


MODULES = $(PASS) $(TODO_PASS) $(TODO_TRANSLATE)

VFILES    = $(addsuffix .v,$(MODULES))
VOFILES   = $(patsubst %.v,%.vo,$(VFILES))
COQFLAGS  = ""

main:
	# Call ourselves with -k, so that we see all test outputs,
	# even if some fail
	$(MAKE) -k all

all:  $(VFILES) pass todo_pass todo_translate

pass: $(addsuffix .pass,$(PASS))
	@echo
	@echo -------- END PASS ------------
	@echo

todo_pass: $(foreach f,$(TODO_PASS),$(f).fail)
	@echo
	@echo "Any names printed without errors should be moved from TODO_PASS to PASS"
	@echo -------- END FAIL ------------
	@echo
	@echo "(Errors are expected from now on)"
	@echo

todo_translate: $(foreach f, $(TODO_TRANSLATE), $(f).fail_translate)
	@echo
	@echo "Any names that fail should be moved from TODO_TRANSLATE to TODO_PASS"
	@echo "Any names that pass should be moved from TODO_TRANSLATE to PASS"
	@echo -------- END UNTRANSLATABLE ------------

%.pass : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m (should pass)"; exit 1;\
	 elif ! $(TYPECHECK) $< >&/dev/null;\
	 then echo -e "\033[1;31mfailed\033[0m (should pass)"; exit 1;  \
	 else echo -e "\033[1;32mpassed\033[0m"; \
	 fi

%.fail : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; exit 1; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;31mfailed\033[0m"; \
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

%.fail_translate : %.v
	@/usr/bin/env echo -n "$<: "
	@if ! test -e $<; \
	 then echo -e "\033[1;31mmissing\033[0m"; \
	 elif ! $(TYPECHECK) $< >&/dev/null; \
	 then echo -e "\033[1;33mfailed\033[0m (unexpected)"; exit 1;\
	 else echo -e "\033[1;32mpassed\033[0m (unexpected)"; exit 1; \
	 fi

# Helpers must be compiled on every run, even when regeneration shares the
# previous .vo's timestamp (notably with GNU Make 3.81's one-second resolution).
%.vo : %.v FORCE
	@$(COMPILER) -Q . "" $*.v

# Only TODO_TRANSLATE may omit output or fail translation. Discard partial
# output on failure so .fail_translate sees an untranslated test.
.SECONDEXPANSION:
%.v : FORCE $$(wildcard $(SRC_DIR)/$$*/edits) $$(wildcard $(SRC_DIR)/$$*/preamble.v) $$(wildcard $(SRC_DIR)/$$*/midamble.v) $(SRC_DIR)/%.hs
	@rm -f $*.v
	@if [ -e $(SRC_DIR)/$*/preamble.v ]; then P_ARG="--preamble $(SRC_DIR)/$*/preamble.v"; else P_ARG=; fi;\
	 if [ -e $(SRC_DIR)/$*/midamble.v ]; then M_ARG="--midamble $(SRC_DIR)/$*/midamble.v"; else M_ARG=; fi;\
	 if [ -e $(SRC_DIR)/$*/edits ];      then E_ARG="--edits    $(SRC_DIR)/$*/edits";      else E_ARG=; fi;\
	 $(HS_TO_ROCQ) $(HS_EXTRA) $${E_ARG} -N -e $(SRC_DIR)/renamings $(HS_IMPORT) -o . $${P_ARG} $${M_ARG} $(SRC_DIR)/$*.hs 1>/dev/null || { \
	   rm -f $*.v; test -n "$(filter $*,$(TODO_TRANSLATE))" || exit 1; \
	 }; \
	 if test -z "$(filter $*,$(TODO_TRANSLATE))"; then \
	   test -e $*.v || { echo "$*.v: translation produced no output" >&2; exit 1; }; \
	 fi

Renamed.v: FORCE $(SRC_DIR)/RenameMe.hs $(SRC_DIR)/RenameMe.hs-boot $(SRC_DIR)/RenameMeToo.hs $(SRC_DIR)/RenameMe/edits
	@rm -f Renamed.v
	$(HS_TO_ROCQ) $(HS_EXTRA) -N -e $(SRC_DIR)/RenameMe/edits -e $(SRC_DIR)/renamings $(HS_IMPORT) -o . $(SRC_DIR)/RenameMe.hs $(SRC_DIR)/RenameMeToo.hs 1>/dev/null || { rm -f Renamed.v; exit 1; }
	@test -e Renamed.v || { echo "Renamed.v: translation produced no output" >&2; exit 1; }

RenameModule.v:: Renamed.vo

RocqFromImports.v: Other/Coq/Init/Decimal.vo
RocqFromImports.pass: TYPECHECK = $(COMPILER) -Q . "" 1>/dev/null

# The implicit %.v rule prefixes prerequisites with a nested target's directory.
Other/Coq/Init/Decimal.v: FORCE $(SRC_DIR)/Other/Coq/Init/Decimal.hs $(SRC_DIR)/Other/Coq/Init/Decimal/edits
	@rm -f $@
	$(HS_TO_ROCQ) $(HS_EXTRA) -N -e $(SRC_DIR)/Other/Coq/Init/Decimal/edits -e $(SRC_DIR)/renamings $(HS_IMPORT) -o . $(SRC_DIR)/Other/Coq/Init/Decimal.hs 1>/dev/null || { rm -f $@; exit 1; }
	@test -e $@ || { echo "$@: translation produced no output" >&2; exit 1; }

# We always want to re-build the .v files, to test the current build of hs-to-rocq
FORCE:

clean:
	rm -rf */*.vo */*.glob */*.v.d *.vo *.vok *.vos *.v.d *.glob *.h2ci .*.aux *.hi *.o *.hi-boot *.o-boot $(VFILES) Renamed.v _CoqProject Makefile.coq *~
	rm -f Other/Coq/Init/Decimal.v Other/Coq/Init/Decimal.h2ci Other/Coq/Init/Decimal.vo Other/Coq/Init/Decimal.vok Other/Coq/Init/Decimal.vos Other/Coq/Init/Decimal.glob Other/Coq/Init/.Decimal.aux

.SECONDARY: $(VFILES) Other/Coq/Init/Decimal.v

.PHONY: main all pass todo_pass todo_translate FORCE clean
