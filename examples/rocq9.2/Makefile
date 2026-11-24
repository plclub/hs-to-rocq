SHELL := bash

ROCQ ?= rocq
COQC ?= $(ROCQ) c

# Project libraries come only from the two local -Q roots, not a caller's path.
export COQPATH :=
export ROCQPATH :=

all: base-thy

check-version:
	@version="$$($(COQC) --print-version)" && \
	  case "$$version" in 9.2\ *|9.2.*\ *) ;; \
	    *) printf 'Rocq 9.2 required; compiler reports: %s\n' "$$version" >&2; exit 1 ;; esac
	@version="$$($(ROCQ) makefile --version)" && \
	  case "$$version" in 'The Rocq Prover, version 9.2'|'The Rocq Prover, version 9.2'$$'\n'*|'The Rocq Prover, version 9.2.'*) ;; \
	    *) printf 'Rocq 9.2 makefile required; reports: %s\n' "$$version" >&2; exit 1 ;; esac

base: check-version
	$(MAKE) -C base-src vfiles
	cd base && $(ROCQ) makefile -f _CoqProject -o Makefile
	$(MAKE) -C base COQC='$(COQC)'

base-thy: base
	$(MAKE) -C base-thy-src vfiles
	cd base-thy && $(ROCQ) makefile -f _CoqProject -o Makefile
	$(MAKE) -C base-thy COQC='$(COQC)'

vfiles: check-version
	$(MAKE) -C base-src vfiles
	$(MAKE) -C base-thy-src vfiles

check: base-thy
	$(MAKE) -C base-thy-src check
	$(COQC) -w +deprecated-dirpath-Coq -Q base "" -Q base-thy Proofs checks/LoadPaths.v
	$(COQC) -w +deprecated-dirpath-Coq -Q base "" -Q checks Rocq92Checks checks/Unfoldr.v
	$(ROCQ) check -silent -Q base "" -Q base-thy Proofs -Q checks Rocq92Checks \
	  Proofs.GHC.Base Proofs.GHC.List Proofs.Data.Foldable \
	  Proofs.Data.Traversable Proofs.Data.Functor.Identity Data.OldList Rocq92Checks.Unfoldr

clean:
	$(MAKE) -C base-src clean
	$(MAKE) -C base-thy-src clean
	rm -f checks/*.vo checks/*.vos checks/*.vok checks/*.glob checks/.*.aux

.PHONY: all check-version base base-thy vfiles check clean
