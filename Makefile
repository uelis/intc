all: opt

byte:
	corebuild -j 0 -cflags "-g" intc.byte

opt:
	corebuild -quiet -j 0 -cflags "-g" intc.native

tags:
	otags *.ml *.mli

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intc.byte intc.native *.ll *.bc 
