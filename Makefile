srcs = ind_obj.v outcome.v
docdir = ./docs
vobjs = $(srcs:.v=.vo)
targets = $(vobjs)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)

outcome.vo: ind_obj.vo

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc -g --utf8 -d $(docdir) $(srcs)
	-cp $(docdir)/mycoqdoc.css $(docdir)/coqdoc.css

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
