all: pdfs

DOTS=$(shell echo *.dot) 

PDFS=$(patsubst %.dot,%.pdf,$(DOTS))

pdfs: $(PDFS)

# Cap the size so that LaTeX doesn't choke.
%.pdf: %.dot # Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

%.svg: %.dot # Makefile
	dot -Tsvg $< | sed -e 's/<svg width.*/<svg/'> $@

# The sed command remove page dimensions to make the results self-scaling

%.png: %.dot
	dot -Gdpi=200 -Tpng $< -o $@
