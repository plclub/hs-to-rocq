include ../../common.mk

.PHONY: all check lint check-edits check-required test-checks verify-source clean

all: check-required

MYPY ?= uvx mypy
RUFF ?= uvx ruff
SHELLCHECK ?= shellcheck

check: lint
	$(MAKE) test-checks
	$(MAKE) check-required

lint:
	$(MYPY) --strict --cache-dir=build/mypy $(wildcard *.py)
	$(RUFF) check --no-cache $(wildcard *.py)
	$(SHELLCHECK) check-ghc checked-tool counterexample/check install-itree-pins test-checks.sh test-vc1

check-edits:
	python3 build-example.py --check-edits

check-required:
	python3 verify-source.py --dependencies
	python3 build-example.py

test-checks:
	bash test-checks.sh

verify-source:
	python3 verify-source.py

clean:
	rm -rf lib build __pycache__
