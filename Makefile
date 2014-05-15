all: opt

byte:
	corebuild -cflags "-g" intc.native

opt:
	corebuild -cflags "-g" intc.native

tags:
	otags *.ml *.mli

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intc.byte intc.native *.ll *.bc 
