include ../../common.mk

.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

ROCQ ?= rocq
COQC ?= $(ROCQ) c
FOUNDATIONS := ../rocq9.2
OUT := lib
MODULES := Data/FingerTree Data/IntervalMap/FingerTree Data/PriorityQueue/FingerTree
VFILES := $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))
VOFILES := $(VFILES:.v=.vo)
CORE_THEORIES := CoreSize CoreModel CoreOperations CoreSearch CoreContext CoreInstances ApplicativeValidity CoreTraversal
PRIORITY_THEORIES := PriorityModel PriorityOperations PriorityRegression
INTERVAL_THEORIES := IntervalModel IntervalOperations IntervalLaws
THEORIES := $(basename $(notdir $(wildcard theories/*.v)))
THEORY_VOFILES := $(addprefix theories/,$(addsuffix .vo,$(THEORIES)))
SOURCE_PIN := 2f303a410c95802a2824b6dd54a0610fa5329858
OWNED_EDITS := edits $(foreach module,$(MODULES),$(wildcard module-edits/$(module)/edits))
OWNED_SUPPORT := $(foreach module,$(MODULES),$(wildcard module-edits/$(module)/preamble.v module-edits/$(module)/midamble.v))
SOURCE_AUDITS := module-edits/Data/FingerTree/CoreAudit.v module-edits/Data/IntervalMap/FingerTree/IntervalAudit.v module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.v

export COQPATH :=
export ROCQPATH :=

HS_OPTS := --target-version 9.0 -N \
  --iface-dir $(FOUNDATIONS)/base --iface-dir $(OUT) \
  -i fingertree --ghc -DTESTING --dependency-dir deps -o $(OUT)
LOAD_PATHS := -Q $(FOUNDATIONS)/base "" -Q $(FOUNDATIONS)/base-thy Proofs -Q $(OUT) "" -Q theories FingerTreeProofs

all: coq proofs

check-source:
	@test "$$(git -C fingertree rev-parse HEAD)" = "$(SOURCE_PIN)"
	git -C fingertree diff --exit-code $(SOURCE_PIN) -- .
	@test -z "$$(git -C fingertree status --porcelain=v1)"

# Check owner inputs before translation or foundation/proof builds. The inherited
# base edits retain their separate policy; aliases reset at each --edits input.
source-policy: source-policy.yaml SourcePolicy.hs check-source-policy.hs check-source-inventory.py $(SOURCE_AUDITS) $(OWNED_EDITS) $(OWNED_SUPPORT)
	mkdir -p deps
	python3 check-source-inventory.py --required > deps/source-required.txt.tmp
	mv deps/source-required.txt.tmp deps/source-required.txt
	stack --allow-different-user exec -- runghc -package=hs-to-rocq -i. check-source-policy.hs \
	  --policy source-policy.yaml --required deps/source-required.txt \
	  $(addprefix --edits ,$(OWNED_EDITS)) $(addprefix --support ,$(OWNED_SUPPORT))

foundations: source-policy
	$(MAKE) -C $(FOUNDATIONS) ROCQ='$(ROCQ)' COQC='$(COQC)'

# Eq and Ord are renamed to the compiled GHC.Base dictionaries by these edits.
# Skipping their original module would also discard the required stock-derived
# instances in this example. Keep the authoritative guidance otherwise intact.
deps/base.edits: ../base-src/edits Makefile
	mkdir -p deps
	test "$$(sed -n '/^skip module GHC\.Classes$$/p' $< | wc -l | tr -d ' ')" = 1
	sed '/^skip module GHC\.Classes$$/d' $< > $@.tmp
	mv $@.tmp $@

vfiles: $(VFILES)

# Force regeneration, including direct targets, to reject stale sources and
# interfaces after a translator change or a failed previous attempt.
.SECONDEXPANSION:
$(VFILES): $(OUT)/%.v: FORCE fingertree/%.hs edits deps/base.edits $$(wildcard module-edits/$$*/edits module-edits/$$*/preamble.v module-edits/$$*/midamble.v) | source-policy check-source foundations
	mkdir -p deps $(dir $@)
	rm -f $@ $(@:.v=.h2ci)
	$(HS_TO_ROCQ) $(HS_OPTS) \
	  $(addprefix -e ,$(wildcard module-edits/$*/edits)) \
	  -e edits -e deps/base.edits \
	  $(addprefix -p ,$(wildcard module-edits/$*/preamble.v)) \
	  $(addprefix --midamble ,$(wildcard module-edits/$*/midamble.v)) \
	  fingertree/$*.hs || { status=$$?; rm -f $@ $(@:.v=.h2ci); exit $$status; }
	test -s $@ && test -s $(@:.v=.h2ci) || { rm -f $@ $(@:.v=.h2ci); exit 1; }
	python3 check-source-inventory.py --module '$*' || { status=$$?; rm -f $@ $(@:.v=.h2ci); exit $$status; }

$(OUT)/Data/IntervalMap/FingerTree.v $(OUT)/Data/PriorityQueue/FingerTree.v: | $(OUT)/Data/FingerTree.v

coq: $(VOFILES)

$(OUT)/%.vo: $(OUT)/%.v FORCE
	rm -f $@
	$(COQC) -w +deprecated-dirpath-Coq $(LOAD_PATHS) $<

$(OUT)/Data/IntervalMap/FingerTree.vo $(OUT)/Data/PriorityQueue/FingerTree.vo: $(OUT)/Data/FingerTree.vo
$(OUT)/Data/IntervalMap/FingerTree.vo $(OUT)/Data/PriorityQueue/FingerTree.vo: theories/CoreSize.vo

proofs: $(THEORY_VOFILES)

# Compile each theory and audit every exported constant against its exact
# permitted assumption set. FORCE and removal of old objects reject stale proofs.
theories/%.vo: theories/%.v theories/check-assumptions.py theories/assumptions.json FORCE
	rm -f $@
	python3 theories/check-assumptions.py --rocq '$(ROCQ)' $*

theories/CoreSize.vo theories/CoreModel.vo theories/ApplicativeValidity.vo: $(OUT)/Data/FingerTree.vo
theories/CoreOperations.vo: theories/CoreModel.vo theories/CoreSize.vo
theories/CoreSearch.vo: theories/CoreOperations.vo theories/CoreSize.vo
theories/CoreContext.vo theories/CoreInstances.vo: theories/CoreOperations.vo
theories/CoreTraversal.vo: theories/CoreModel.vo theories/CoreOperations.vo theories/CoreContext.vo theories/ApplicativeValidity.vo
theories/PriorityModel.vo theories/PriorityRegression.vo: $(OUT)/Data/PriorityQueue/FingerTree.vo
theories/PriorityOperations.vo: theories/PriorityModel.vo theories/CoreSearch.vo theories/CoreSize.vo
theories/IntervalModel.vo: $(OUT)/Data/IntervalMap/FingerTree.vo theories/CoreSearch.vo
theories/IntervalOperations.vo: theories/IntervalModel.vo theories/CoreTraversal.vo theories/CoreSize.vo
theories/IntervalLaws.vo: theories/IntervalOperations.vo
theories/ApplicationLaws.vo: theories/CoreInstances.vo theories/PriorityOperations.vo theories/IntervalOperations.vo

kernel-check: coq proofs
	$(ROCQ) check -silent $(LOAD_PATHS) Data.FingerTree Data.IntervalMap.FingerTree Data.PriorityQueue.FingerTree $(addprefix FingerTreeProofs.,$(THEORIES))

core-check: $(addprefix theories/,$(addsuffix .vo,$(CORE_THEORIES)))
	$(COQC) -w +deprecated-dirpath-Coq $(LOAD_PATHS) -Q module-edits/Data/FingerTree FingerTreeChecks module-edits/Data/FingerTree/CoreAudit.v
	$(ROCQ) check -silent $(LOAD_PATHS) -Q module-edits/Data/FingerTree FingerTreeChecks Data.FingerTree $(addprefix FingerTreeProofs.,$(CORE_THEORIES)) FingerTreeChecks.CoreAudit

interval-check: $(addprefix theories/,$(addsuffix .vo,$(INTERVAL_THEORIES)))
	$(COQC) -w +deprecated-dirpath-Coq $(LOAD_PATHS) -Q module-edits/Data/IntervalMap/FingerTree IntervalChecks module-edits/Data/IntervalMap/FingerTree/IntervalAudit.v
	$(ROCQ) check -silent $(LOAD_PATHS) -Q module-edits/Data/IntervalMap/FingerTree IntervalChecks Data.IntervalMap.FingerTree $(addprefix FingerTreeProofs.,$(INTERVAL_THEORIES)) IntervalChecks.IntervalAudit

priority-check: $(addprefix theories/,$(addsuffix .vo,$(PRIORITY_THEORIES)))
	python3 module-edits/Data/PriorityQueue/FingerTree/check-priority-audit.py --rocq '$(ROCQ)'
	$(ROCQ) check -silent $(LOAD_PATHS) -Q $(FOUNDATIONS)/checks Rocq92Checks -Q module-edits/Data/PriorityQueue/FingerTree PriorityChecks \
	  Data.OldList Rocq92Checks.Unfoldr Data.PriorityQueue.FingerTree PriorityChecks.PriorityAudit $(addprefix FingerTreeProofs.,$(PRIORITY_THEORIES))

clean:
	rm -rf lib/Data deps
	rm -f $(foreach ext,vo vos vok glob,$(addprefix theories/,$(addsuffix .$(ext),$(THEORIES)))) $(addprefix theories/.,$(addsuffix .aux,$(THEORIES)))
	rm -f module-edits/Data/FingerTree/CoreAudit.vo module-edits/Data/FingerTree/CoreAudit.vos module-edits/Data/FingerTree/CoreAudit.vok module-edits/Data/FingerTree/CoreAudit.glob module-edits/Data/FingerTree/.CoreAudit.aux
	rm -f module-edits/Data/IntervalMap/FingerTree/IntervalAudit.vo module-edits/Data/IntervalMap/FingerTree/IntervalAudit.vos module-edits/Data/IntervalMap/FingerTree/IntervalAudit.vok module-edits/Data/IntervalMap/FingerTree/IntervalAudit.glob module-edits/Data/IntervalMap/FingerTree/.IntervalAudit.aux
	rm -f module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.vo module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.vos module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.vok module-edits/Data/PriorityQueue/FingerTree/PriorityAudit.glob module-edits/Data/PriorityQueue/FingerTree/.PriorityAudit.aux

FORCE:

.PHONY: all check-source source-policy foundations vfiles coq proofs kernel-check core-check interval-check priority-check clean FORCE
