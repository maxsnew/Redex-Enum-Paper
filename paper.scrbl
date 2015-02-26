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
                 #"\\newenvironment{proof_idea}[1][Proof Idea]{\\begin{trivlist}\n"
                 #"\\item[\\hskip \\labelsep {\\bfseries #1}]}{\\end{trivlist}}\n"
                 #"\\newcommand{\\qed}{\\nobreak \\ifvmode \\relax \\else\n"
                 #"\\ifdim\\lastskip<1.5em \\hskip-\\lastskip\n"
                 #"\\hskip1.5em plus0em minus0.5em \\fi \\nobreak\n"
                 #"\\vrule height0.75em width0.5em depth0.25em\\fi}\n"

                 ;; map the ℕ character
                 #"\\DeclareUnicodeCharacter{2115}{$\\mathbb{N}$}\n"
                 
                 ;; used for the table of the bugs
                 #"\\newenvironment{IntroWrapFigure}"
                 #"{\\begin{wrapfigure}{r}{4in}}"
                 #"{\\end{wrapfigure}}\n"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  Ffeat: Fair Functional Enumeration of Algebraic Types
}
@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]

@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]

@authorinfo["Jay McCarthy"
            "Vassar College"
            "jay.mccarthy@gmail.com"]

@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]

@abstract{
  This paper reports on the design of combinators
  for building efficient bijections between the 
  naturals numbers (or a prefix of them) and algebraic
  datatypes constructed by sums, recursion, and (possibly
  dependent) pairs.
  
  Our enumeration combinators support a new property
  we call fairness. Intuitively the result of fair combinator 
  indexes into its argument combinators equally when constructing
  its result. For example, extracting the
  @raw-latex{$n$}th element from our enumeration of three-tuples
  indexes about @raw-latex{$\sqrt[3]{n}$} elements into each
  of its components instead of, say, indexing @raw-latex{$\sqrt[2]{n}$}
  into one and @raw-latex{$\sqrt[4]{n}$} into the other two as you would 
  if you build a three-tuple out of nested pairs. The paper
  develops the theory of fairness and contains proofs establishing
  fairness of our combinators and a proof that some combinations of 
  fair combinators are not fair.
  
  The design of our combinators is driven by our primary
  application, property-based testing in Redex. The paper also
  reports on how our combinators can support enumeration for arbitrary
  Redex models and an empirical comparison between enumeration-based 
  property generation and ad hoc random generation, showing
  that the strategies are complementary. 
}

@include-section["combinators.scrbl"]

@include-section["fair-intro.scrbl"]

@include-section["redex-enumeration.scrbl"]

@include-section["evaluation.scrbl"]

@include-section["related.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

