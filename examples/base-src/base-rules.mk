# Shared generation bookkeeping. The caller sets BASE_SRC and OUT and includes
# modules.mk before this file; translation and manual-file recipes stay local.

.DELETE_ON_ERROR:

# An existing project file is also a completion marker for top-level builds.
# Invalidate it before visiting any source, including on failed regeneration.
.PHONY: prepare-project
prepare-project:
	mkdir -p $(OUT)
	rm -f $(OUT)/_CoqProject

$(VFILES): | prepare-project

# hs-to-rocq writes dependency files but does not create their parent directory.
# This must hold for direct targets as well as serial and parallel vfiles builds.
$(VFILES_GEN) $(VFILES_RENAMED) $(VFILES_SPECIAL) $(VFILES_DROPIN): | deps

deps:
	mkdir -p $@

# Publish only after all sources succeed. The phony prerequisite also refreshes
# the marker after prepare-project removes a previously complete project file.
$(OUT)/_CoqProject: Makefile $(BASE_SRC)/modules.mk $(BASE_SRC)/base-rules.mk prepare-project $(VFILES)
	mkdir -p $(OUT)
	{ echo '-Q . ""'; \
	  echo $(addsuffix .v,$(HANDMOD)) $(addsuffix .v,$(EARLY_MODULES)); \
	  echo $(addsuffix .v,$(MODULES)); \
	  echo $(addsuffix .v,$(RENAMED)); \
	  echo $(addsuffix .v,$(SPECIAL_MODULES)); \
	  echo $(addsuffix .v,$(DROPIN)); \
	} > $@.tmp
	mv $@.tmp $@
