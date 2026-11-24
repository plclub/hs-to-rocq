# Both wrappers have the same depth. This keeps the authoritative sources,
# module inventory, manual interfaces, local deps, and failure cleanup intact.
# The translator's 9.0 target supplies the Rocq-9 namespace, also used by 9.2.
include ../../rocq9.0/base-src/Makefile

# Restore the authoritative unfoldr source only for this foundation. Preserve
# every other OldList edit, preamble, midamble, and the shared generation rule.
GHC_INTERNAL_EDITS_Data/OldList = deps/OldList.edits
$(OUT)/Data/OldList.v: deps/OldList.edits

deps/OldList.edits: $(BASE_SRC)/module-edits/Data/OldList/edits module-edits/Data/OldList/edits Makefile
	mkdir -p deps
	test "$$(sed -n '/^skip Data\.OldList\.unfoldr$$/p' $< | wc -l | tr -d ' ')" = 1
	{ sed '/^skip Data\.OldList\.unfoldr$$/d' $<; \
	  cat module-edits/Data/OldList/edits; } > $@.tmp
	mv $@.tmp $@
