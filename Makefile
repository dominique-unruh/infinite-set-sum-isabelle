
JEDIT_SESSION=HOL-Analysis
ISABELLE_DIR=/opt/Isabelle2021
ISABELLE=$(ISABELLE_DIR)/bin/isabelle

edit :
	"$(ISABELLE)" jedit -l "$(SESSION)" -d . All.thy &

build document/infinite-sums.pdf document/infinite-sums-full.pdf : \
		$(wildcard *.thy) ROOT document/root.tex document/root.bib
	"$(ISABELLE)" build -b -D . -o "document_output=document"

infinite-sums-afp.zip : ROOT document/root.tex document/root.bib Infinite_Sum_Misc.thy Infinite_Sum.thy Infsetsum_Infsum.thy Infsetsum.thy LICENSE README.md
	rm -rf tmp
	mkdir -p tmp/Infinite_Sums
	cp $^ tmp/Infinite_Sums
	cd tmp && zip -r $@ Infinite_Sums
	mv tmp/$@ .

show : document/infinite-sums.pdf
	evince $^ &
