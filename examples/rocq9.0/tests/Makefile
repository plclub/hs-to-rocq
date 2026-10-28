# Makefile for Rocq 9.0 unit tests.
# Reuses test .hs files from examples/tests/ via the shared test-rules.mk.
# Rocq 9 replaced coqc with `rocq c`; set COMPILER accordingly.

include ../../../common.mk

# Do not let Rocq's compatibility alias hide missed namespace rewrites.
COMPILER  = rocq c -w +deprecated-dirpath-Coq
SRC_DIR   = ../../tests
HS_EXTRA  = --target-version 9.0
HS_IMPORT = -i $(SRC_DIR)

include $(SRC_DIR)/test-rules.mk
