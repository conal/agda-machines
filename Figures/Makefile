all: pdfs
# all: jpgs
# all: svgs
# all: pngs

DOTS=$(shell echo *.dot) 

PDFS=$(patsubst %.dot,%.pdf,$(DOTS))
pdfs: $(PDFS)

PNGS=$(patsubst %.dot,%.png,$(DOTS))
pngs: $(PNGS)

SVGS=$(patsubst %.dot,%.svg,$(DOTS))
svgs: $(SVGS)

JPGS=$(patsubst %.dot,%.jpg,$(DOTS))
jpgs: $(JPGS)

# Cap the size so that LaTeX doesn't choke.
%.pdf: %.dot # Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

%.svg: %.dot # Makefile
	dot -Tsvg $< | sed -e 's/<svg width.*/<svg/'> $@

# The sed command remove page dimensions to make the results self-scaling

%.png: %.dot
	dot -Gdpi=200 -Tpng $< -o $@

%.jpg: %.dot
	dot -Gdpi=200 -Tjpg $< -o $@
