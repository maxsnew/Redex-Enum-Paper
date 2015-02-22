#lang scribble/sigplan

@(require "cite.rkt" 
          "util.rkt"
          scribble/core
          scribble/latex-properties
          (except-in scribble/manual author))

@(define extra-tex-code
   (bytes-append #"\\usepackage{pslatex}\n"
                 #"\\usepackage{inconsolata}\n"
                 #"\\usepackage{savesym}\n"
                 #"\\savesymbol{iint}\n"
                 #"\\savesymbol{iiint}\n"
                 #"\\usepackage{amsmath}\n"
                 #"\\usepackage{amsfonts}\n"
                 #"\\usepackage{wrapfig}\n"
                 
                 ;; horrible hack to work around the fact that inconsolata in texlive 2013
                 ;; doesn't have the straight quote character.
                 #"\\savesymbol{textquotesingle}\n"
                 #"\\newcommand{\\textquotesingle}{"
                 #"\\fontfamily{cmtt}\\selectfont{}\\origtextquotesingle}\n"

                 ;; theorem, proof, and \qed definitions from
                 ;; http://www.maths.tcd.ie/~dwilkins/LaTeXPrimer/Theorems.html
                 ;; so that the paper at least runs
                 #"\\newtheorem{theorem}{Theorem}\n"
                 #"\\newenvironment{proof}[1][Proof]{\\begin{trivlist}\n"
                 #"\\item[\\hskip \\labelsep {\\bfseries #1}]}{\\end{trivlist}}\n"
                 #"\\newcommand{\\qed}{\\nobreak \\ifvmode \\relax \\else\n"
                 #"\\ifdim\\lastskip<1.5em \\hskip-\\lastskip\n"
                 #"\\hskip1.5em plus0em minus0.5em \\fi \\nobreak\n"
                 #"\\vrule height0.75em width0.5em depth0.25em\\fi}\n"

                 ;; used for the table of the bugs
                 #"\\newenvironment{IntroWrapFigure}"
                 #"{\\begin{wrapfigure}{r}{4in}}"
                 #"{\\end{wrapfigure}}\n"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  Practical, Fair, and Efficient Enumeration for Algebraic Data-Structures
}
@authorinfo["Max New"
	    "Northwestern University"
	    "max.new@eecs.northwestern.edu"]

@authorinfo["Burke Fetscher"
	    "Northwestern University"
	    "burke.fetscher@eecs.northwestern.edu"]

@authorinfo["Jay McCarthy"
	    "Vassar College"
	    "TODO@vassar_I_guess.edu"]

@authorinfo["Robert Bruce Findler"
	    "Northwestern University"
	    "robby@eecs.northwestern.edu"]

@abstract{
 This paper reports on the design of a set of
 enumeration combinators that are efficient, fair, 
 and practical. They are efficient because most
 of the combinators produce enumerations that
 support indexing in time proportional to the
 log of the given index. In concrete terms, this
 means that we can typically compute the 
 @raw-latex{$2^{100,000}$}th element of an enumeration 
 in a few milliseconds.
 
 Fairness means that when the combinators build a new result
 enumeration out of other ones, indexing into the result enumerator
 does not index disproportionally
 far into just a subset of the given enumerators. For example, 
 this means that enumeration of the
 @raw-latex{$n$}th element of an enumeration of three-tuples
 indexes about @raw-latex{$\sqrt[3]{n}$} elements into each
 of its components.
 
 Our combinators are practical because they support the
 entire language of Redex models, providing a new generator
 for Redex's property-based testing. The paper reports
 on an empirical comparison between enumeration-based 
 property generation and ad hoc random generation, showing
 that enumeration is more effective than ad hoc random
 generation in short time-frames. While Redex is our main 
 application of enumeration, our enumerators also support
 a video-game programming engine and give us the opportunity
 for some new game mechanics.
}

@include-section["intro.scrbl"]

@include-section["combinators.scrbl"]

@include-section["fair-intro.scrbl"]

@include-section["redex-enumeration.scrbl"]

@include-section["evaluation.scrbl"]

@include-section["related.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

