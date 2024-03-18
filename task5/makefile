ALEX = tokenizer
HAPPY = parser
HSFILE = Main.hs

all:
	alex -g ${ALEX}.x
	happy -a -g -c ${HAPPY}.y
	ghc -O2 ${HSFILE} ${ALEX}.hs ${HAPPY}.hs

run:
	./Main
