srcs = ind_obj.v
docdir = ./docs
vobjs = $(srcs:.v=.vo)
targets = $(vobjs)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc --gallina --utf8 -d $(docdir) $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
