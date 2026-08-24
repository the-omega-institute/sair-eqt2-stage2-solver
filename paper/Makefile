TEX=pdflatex
BIB=bibtex

.PHONY: all plain acm clean

all: plain

plain:
	$(TEX) -interaction=nonstopmode -halt-on-error "\def\PLAINARTICLE{1}\input{main.tex}"
	$(BIB) main
	$(TEX) -interaction=nonstopmode -halt-on-error "\def\PLAINARTICLE{1}\input{main.tex}"
	$(TEX) -interaction=nonstopmode -halt-on-error "\def\PLAINARTICLE{1}\input{main.tex}"

acm:
	$(TEX) -interaction=nonstopmode -halt-on-error main.tex
	$(BIB) main
	$(TEX) -interaction=nonstopmode -halt-on-error main.tex
	$(TEX) -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf

anon:
	pdflatex -interaction=nonstopmode "\\def\\ANONSUBMISSION{1}\\def\\PLAINARTICLE{1}\\input{main.tex}" >/dev/null && pdflatex -interaction=nonstopmode "\\def\\ANONSUBMISSION{1}\\def\\PLAINARTICLE{1}\\input{main.tex}" >/dev/null
