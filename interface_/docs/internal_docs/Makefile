

handling_extensibility.pdf: handling_extensibility.tex
	pdflatex handling_extensibility.tex
	pdflatex handling_extensibility.tex

#have short so we can make it run only once
short: handling_extensibility.tex
	pdflatex handling_extensibility.tex

part-clean:
	rm *~ *.aux *.log *.out

clean:
	rm *~ *.aux *.log *.out *.pdf
