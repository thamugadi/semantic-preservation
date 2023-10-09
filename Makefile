all:
	coq_makefile -f _CoqProject -o coq_makefile
	make -f coq_makefile
clean:
	make -f coq_makefile clean
	rm coq_makefile coq_makefile.conf
