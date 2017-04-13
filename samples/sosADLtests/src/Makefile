
COQC=coqc
COQFLAGS=-R ../../../typesystem/SosADL SosADL

SOURCES=$(wildcard *.v)
TARGETS=$(patsubst %.v,%.vo,$(SOURCES))
GLOBS=$(patsubst %.v,%.glob,$(SOURCES))

all: $(TARGETS)

%.vo:%.v
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f $(TARGETS) $(GLOBS)
