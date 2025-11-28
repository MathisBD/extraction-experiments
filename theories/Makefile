all:
	ocamlfind ocamlopt -package rocq-runtime.lib,extraction-experiments.plugin -shared -runtime-variant _pic -o hello.cmxs hello.ml

clean:
	rm *.cmi *.cmx *.cmxs *.o