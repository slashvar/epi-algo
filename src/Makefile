# Makefile for epi-algo

PREFIX=${HOME}/bin

OCBUILD=ocamlbuild.native
ML=ast.ml builtins.ml main.ml mangling.ml memory.ml native_data.ml \
   primitives.ml t_graphe.ml typing.ml lexer.mll parser.mly

all: epi-algo

epi-algo: _build/main.native
	cp _build/main.native epi-algo

epi-algo.byte: _build/main.byte
	cp _build/main.byte epi-algo.byte

_build/main.native: _tags ${ML}
	${OCBUILD} main.native

_build/main.byte: _tags ${ML}
	${OCBUILD} main.byte

install: epi-algo
	mkdir -p ${PREFIX}
	cp epi-algo ${PREFIX}

uninstall:
	rm -f ${PREFIX}/epi-algo

clean-build::
	rm -f *~
	${OCBUILD} -clean

clean:: clean-build
	rm -f epi-algo epi-algo.byte

# END
