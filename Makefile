
JEDIT_SESSION=HOL-Analysis
ISABELLE_DIR=/opt/Isabelle2021
ISABELLE=$(ISABELLE_DIR)/bin/isabelle

edit :
	"$(ISABELLE)" jedit -l "$(SESSION)" -d . All.thy &

build document/infinite-sum.pdf document/infinite-sum-full.pdf : \
		$(wildcard *.thy) ROOT document/root.tex
	"$(ISABELLE)" build -b -D . -o "document_output=document"

show : document/infinite-sum.pdf
	evince $^ &
