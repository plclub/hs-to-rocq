include ../../common.mk

.PHONY: all check lint check-edits check-required check-deadlock-local check-cond-haskell test-checks verify-source clean

all: check-required

MYPY ?= uvx mypy
RUFF ?= uvx ruff
SHELLCHECK ?= shellcheck

check: lint
	$(MAKE) check-cond-haskell
	$(MAKE) test-checks
	$(MAKE) check-final

PYTHON_SOURCES := $(wildcard *.py) tests/check-deadlock-local.py
lint:
	$(MYPY) --strict --cache-dir=build/mypy $(PYTHON_SOURCES)
	$(RUFF) check --no-cache $(PYTHON_SOURCES)
	$(SHELLCHECK) check-ghc checked-tool counterexample/check counterexample/check-haskell install-itree-pins test-checks.sh test-vc1

check-cond-haskell: verify-source
	bash counterexample/check-haskell

check-edits:
	python3 build-example.py --check-edits

check-deadlock-local:
	rm -rf build/deadlock-local
	python3 tests/check-deadlock-local.py --output build/deadlock-local

.PHONY: check-final
check-required check-final:
	python3 verify-source.py --dependencies
	python3 build-example.py $(if $(filter 1,$(SCRATCH)),--scratch) $(if $(filter check-final,$@),--final)

test-checks:
	bash test-checks.sh

verify-source:
	python3 verify-source.py

clean:
	rm -rf lib build __pycache__
