all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force

test_extraction:
	@cd "extraction/"; \
		ocamlc -c insert.mli insert.ml isort.mli isort.ml; \
		ocamlc -c merge.mli merge.ml msort.mli msort.ml; \
		ocamlc -c psort.mli psort.ml; \
		ocamlc -c qsort.mli qsort.ml; \
		ocamlc -c test_extraction.ml; \
		ocamlc unix.cma -o test_extraction insert.cmo isort.cmo merge.cmo msort.cmo psort.cmo qsort.cmo test_extraction.cmo; \
		ocamlrun test_extraction
