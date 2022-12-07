MAIN = main.tex

BASE := $(basename $(MAIN))
SRCEXT := $(patsubst $(BASE).%,%,$(MAIN))
BIBFILES := $(wildcard bib/*.bib) $(wildcard *.bib)
STYLINK := $(notdir $(wildcard *.sty))
STYFILES := $(sort $(STYLINK) $(wildcard *.sty))
TEXFILES := $(sort $(MAIN) $(wildcard *.tex) $(STYFILES)) $(sort $(MAIN) $(wildcard figures/*.tex) $(STYFILES))
PLOT_SCRIPTS := $(wildcard scripts/*) $(wildcard scripts/proc_rslt/*)
PLOT_LOGS := $(wildcard logs/*.log)
PLOTS := $(patsubst logs/%.log, graphs/%.pdf, $(PLOT_LOGS))

LATEX = pdflatex
BIBTEX = bibtex -min-crossrefs=1000
PS2PDF = ps2pdf


# by default, not extended mode
# change this to 1 if you want extended mode by default
EXTENDED ?= 0
ifeq ($(EXTENDED),1)
EXTDEF := \def\buildextended{}
else
EXTDEF :=
endif

# by default, editing marks
# change this to 0 if you want no edit marks by default
EDITING ?= 1
ifeq ($(EDITING),1)
EDITDEF :=
else
EDITDEF := \def\noeditingmarks{}
endif

# put latexmk in auto mode?
AUTO ?= 0
ifeq ($(AUTO),1)
AUTODEF := -pvc
else
AUTODEF :=
endif

all: $(BASE).pdf

#.headline:
#	$(MAKE) -C headline

#.images: headline/headline.eps  $(addsuffix /*.eps,$(IMAGES)) $(addsuffix /*.tex,$(IMAGES))
#	for i in $(IMAGES); do $(MAKE) -C $$i; done
#	touch $@

graphs/%.pdf: scripts/%.rb logs/%.log
	mkdir -p graphs
	$< | gnuplot > $@.eps
	epstopdf --outfile=$@ $@.eps
	rm $@.eps

.SECONDEXPANSION:
$(FIGURES): %.tex: scripts/%.sh scripts/proc_rslt/%.rb $$(wildcard %-skeleton.tex) $$(wildcard logs/%/*.txt)
	mkdir -p graphs
	$< $(lastword $+)
	touch $@

%.pdf: %.eps
	perl -ne 'exit 1 unless /\n/' $< \
		|| perl -p -i -e 's/\r/\n/g' $<
	epstopdf --outfile=$@ $<

diff:
	echo "Build the latexdiff"
	echo '$(EXTDEF)$(EDITDEF)\input{latexdiff.tex}' > latexdiff.tltx
	latexmk $(AUTODEF) -pdf -pdflatex='pdflatex --enable-write18 %O %S' latexdiff.tltx
	rm -f latexdiff.tltx

$(BASE).pdf: %.pdf: %.$(SRCEXT) $(TEXFILES) $(BIBFILES) $(FIGURES) $(PLOT_SCRIPTS) $(PLOTS)
	echo '$(EXTDEF)$(EDITDEF)\input{$<}' > $(BASE).tltx
	latexmk $(AUTODEF) -pdf -pdflatex='pdflatex --enable-write18 %O %S' $(BASE).tltx
	rm -f $(BASE).tltx

show: $(BASE).pdf
	xpdf -fullscreen $(BASE).pdf

osx: $(BASE).pdf
	open $(BASE).pdf

double:
	for i in $(TEXFILES); do perl double.pl $$i; done

clean:
		rm -f graphs/* scripts/dat/*
		rm -f $(BASE).ps $(BASE).pdf
		rm -f *.dvi *.aux *.log *.bbl *.blg *.lof *.lot *.toc *.bak *.out .images $(BASE).fdb_latexmk $(BASE).fls $(BASE).tltx
		for i in $(IMAGES); do $(MAKE) -C $$i clean; done

spell:
	make clean
	for i in $(wildcard *.tex); do aspell -p ./aspell.words -c $$i; done
