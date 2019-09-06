compile:
	ocamlbuild -use-ocamlfind -I src a.native

dAppTest: 
	ocamlbuild -use-ocamlfind -I src dAppTest.native
	./dAppTest.native

isPathAndOtherTest: 
	ocamlbuild -use-ocamlfind -I src isPathAndOtherTest.native
	./isPathAndOtherTest.native

isPathTest:
	ocamlbuild -use-ocamlfind -I src isPathTest.native
	./isPathTest.native	

unifyTest:
	ocamlbuild -use-ocamlfind -I src unifyTest.native
	./unifyTest.native

bottles:
	ocamlbuild -use-ocamlfind -I src bottles.native
	./bottles.native

sortoTest:
	ocamlbuild -use-ocamlfind -I src sortoTest.native
	./sortoTest.native
	
clear:
	$(RM) -r _build *.native

.PHONY: dAppTest isPathAndOtherTest isPathTest unifyTest bottles
