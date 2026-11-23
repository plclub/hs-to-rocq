.DEFAULT_GOAL := all

# The generated rules track subsequent changes to _CoqProject.
Makefile.coq:
	rocq makefile -f _CoqProject -o $@

include Makefile.coq
