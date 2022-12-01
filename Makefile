LIB_NAME=Lib
LIB_DIR=lib

# TODO(nikita): we want Neuromorphic.v to compile first so we
# hardcode the order for now
# LIB_FILES=${wildcard ${LIB_DIR}/*.v}
LIB_FILES=lib/Neuromorphic.v lib/Leak.v lib/NoLeak.v
LIB_BASE=${basename ${LIB_FILES}}
LIB_VO_FILES=${addsuffix .vo,${LIB_BASE}}

EXAMPLE=Examples.vo

CC=coqc
CFLAGS=-R ${LIB_DIR} ${LIB_NAME}

lib: ${LIB_VO_FILES} Makefile ;

${LIB_VO_FILES} : lib/%.vo : Makefile lib/%.v
	${CC} ${CFLAGS} lib/$*.v

${EXAMPLE} : %.vo : ${LIB_VO_FILES} %.v Makefile
	${CC} ${CFLAGS} $*.v

example: ${EXAMPLE} Makefile ;

clean:
	rm -f lib/.*.aux lib/*.vo lib/*.vok lib/*.vos lib/*.glob .*.aux *.vo *.vok *.vos *.glob