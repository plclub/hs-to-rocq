SOURCE = ../../../base-thy
OUT = ../base-thy
MODULES = GHC/Base GHC/List Data/Foldable Data/Traversable Data/Functor/Identity
VFILES = $(addprefix $(OUT)/,$(addsuffix .v,$(MODULES)))

all: vfiles

vfiles: $(OUT)/_CoqProject $(VFILES)

.DELETE_ON_ERROR:

prepare-project:
	mkdir -p $(OUT)
	rm -f $(OUT)/_CoqProject

$(VFILES): | prepare-project

$(OUT)/%.v: $(SOURCE)/%.v ../adapt.py Makefile
	rm -f $@
	python3 ../adapt.py $< $@

# Publish the completion marker only after every adapted source succeeds.
$(OUT)/_CoqProject: _CoqProject Makefile prepare-project $(VFILES)
	cp $< $@.tmp
	mv $@.tmp $@

check:
	@set -e; for module in $(MODULES); do \
	  python3 ../adapt.py --check $(SOURCE)/$$module.v $(OUT)/$$module.v; \
	done

clean:
	rm -rf $(OUT)

.PHONY: all vfiles prepare-project check clean
