all: native

native:
	corebuild -j 0 -cflags "-g" intc.native

test:
	corebuild -j 0 test.native
	corebuild -j 0 test_inline.native
	./test.native
	./test_inline.native inline-test-runner intc -show-counts

locallib:
	corebuild -j 0 -cflags "-g" intlib.cmxa
	ocamlfind remove intlib
	ocamlfind install intlib META _build/intlib.*

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build *.byte *.native

veryclean:
	rm -f *.ssa *.ssa.traced *.ssa.shortcut *.ll *.bc
