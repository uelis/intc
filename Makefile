all: native

native:
	corebuild -j 0 -cflags "-g" intc.native

tests:
	corebuild -j 0 -cflags "-g" intc_tests.native
	./intc_tests.native

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intc.byte intc.native

veryclean:
	rm -f *.ssa *.ssa.traced *.ssa.shortcut *.ll *.bc
