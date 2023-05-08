all: dfa.dot
	dot -Txdot $< | dot2tex -traw --autosize --nominsize > dfa.tex
	sed -i 's/EPSILON/\\epsilon/g' dfa.tex
	sed -i 's/EMPTYSET/\\emptyset/g' dfa.tex
	sed -i 's/NEG/\\neg/g' dfa.tex
	pdflatex dfa.tex

tikz: dfa.dot
	dot -Txdot $< | dot2tex --figonly -traw > dfa.tex
	sed -i 's/EPSILON/\\epsilon/g' dfa.tex
	sed -i 's/EMPTYSET/\\emptyset/g' dfa.tex
	sed -i 's/NEG/\\neg/g' dfa.tex

clean:
	rm *.tex *.pdf *.aux *.log
