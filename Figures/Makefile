all: pdfs

DOTS=$(shell echo *.dot) 

PDFS=$(patsubst %.dot,%.pdf,$(DOTS))

pdfs: $(PDFS)

# Cap the size so that LaTeX doesn't choke.
%.pdf: %.dot # Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@
