all: Makefile.coq
	export TIMED
	@+$(MAKE) -f Makefile.coq all

html: all Makefile.coq
	@+$(MAKE) -f Makefile.coq html
	mv html/*.html website
	rm -rf html

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

mkCoqProject: _CoqProject.in
	yes | cp _CoqProject.in _CoqProject
	find . -name '*.v' | sed "s/\.\///g" >> _CoqProject

Makefile.coq: mkCoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

force Makefile _CoqProject.in: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all html clean force mkCoqProject
