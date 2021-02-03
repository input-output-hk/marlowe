DOCUMENT="article"

all:
	pdflatex --shell-escape $(DOCUMENT).tex
	bibtex $(DOCUMENT)
	pdflatex --shell-escape $(DOCUMENT).tex
	pdflatex --shell-escape $(DOCUMENT).tex

clean:
	rm -f *~ *out *log *aux *toc *bbl *blg *bcf *ptc *acn *acr *alg *idx \
		*run.xml *xdy *-blx.bib *.glo *.ist *lof *.pdf *.glg *.gls *.pyg *.brf
	rm -fr _minted-paper
