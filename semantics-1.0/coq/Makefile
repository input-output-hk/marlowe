_: makefile.coq

makefile.coq: _CoqProject
	coq_makefile $(shell cat _CoqProject) *.v > $@ 2> /dev/null

-include makefile.coq

clean::
	rm makefile.coq CoqMakefile.conf

.PHONY: _
