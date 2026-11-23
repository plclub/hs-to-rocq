include ../../common.mk

.PHONY: all deps check check-layout lint check-edits check-required check-deadlock-local check-cond-haskell test-checks verify-source clean

BUILD_EXAMPLE = python3 scripts/build-example.py $(if $(filter 1,$(SCRATCH)),--scratch)

all:
	$(BUILD_EXAMPLE)

MYPY ?= uvx mypy
RUFF ?= uvx ruff
SHELLCHECK ?= shellcheck

check: check-layout lint
	$(MAKE) check-cond-haskell
	$(MAKE) test-checks
	$(MAKE) check-required

check-layout:
	python3 scripts/check_layout.py

PYTHON_SOURCES := $(wildcard scripts/*.py)
SHELL_SOURCES := $(addprefix scripts/,check-ghc checked-tool \
	check-counterexample check-counterexample-haskell check-deadlock-repair-match \
	test-checks.sh test-vc1)
lint:
	$(MYPY) --strict --cache-dir=build/mypy $(PYTHON_SOURCES)
	$(RUFF) check --no-cache $(PYTHON_SOURCES)
	$(SHELLCHECK) $(SHELL_SOURCES)

check-cond-haskell: verify-source
	bash scripts/check-counterexample-haskell

check-edits:
	python3 scripts/build-example.py --check-edits

deps:
	$(BUILD_EXAMPLE) --deps-only

check-deadlock-local:
	rm -rf build/deadlock-local
	python3 scripts/check-deadlock-local.py --output build/deadlock-local

.PHONY: check-final
check-final: check-required

check-required: check-layout
	$(BUILD_EXAMPLE) --check

test-checks:
	python3 -m unittest discover -s scripts -p test_layout.py
	bash scripts/test-checks.sh

verify-source:
	python3 scripts/verify-source.py

clean:
	@for dir in theories tests; do \
		if test -f $$dir/Makefile.coq; then $(MAKE) -C $$dir -f Makefile.coq clean || exit $$?; fi; \
		rm -f $$dir/*.vo $$dir/*.vos $$dir/*.vok $$dir/*.glob $$dir/.*.aux; \
		rm -f $$dir/Makefile.coq $$dir/Makefile.coq.conf $$dir/.Makefile.coq.d; \
	done
	rm -rf lib build __pycache__ tests/__pycache__ scripts/__pycache__
