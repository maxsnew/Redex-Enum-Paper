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

                 ;; removing these causes problems only for the commented out redex
                 ;; sections below, so get rid of them for now so the paper builds.
                 ;#"\\usepackage{amsmath}\n"
                 ;#"\\usepackage{amsfonts}\n"

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
  Fair Enumeration Combinators
}
@;{
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
}
@abstract{
This paper offers a new property of enumeration combinators
called @emph{fairness} that accepts enumeration combinators
whose results are well-behaved with respect to their
arguments and rejects others.
Intuitively the result of fair combinator indexes into its
argument enumerations equally when constructing its result.
For example, extracting the @texmath{n}th element from
our enumeration of three-tuples indexes about
@texmath{\sqrt[3]{n}} elements into each of its
components instead of, say, indexing
@texmath{\sqrt[2]{n}} into one and
@texmath{\sqrt[4]{n}} into the other two as you would if
you build a three-tuple out of nested pairs. Similarly,
extracting the @raw-latex{n}th element from our
enumeration of a union of three enumerators returns an
element that is @texmath{\frac{n}{3}} into one of the
argument enumerators.

The paper develops presents a semantics of enumeration
combinators, a theory of fairness, proofs establishing
fairness of our new combinators, and proofs that certain
combinations of fair combinators are not fair.

We also report on an evaluation of fairness for the purpose
of finding bugs in operational semantics and type systems.
More precisely, we implemented generators for arbitrary
Redex grammars using our enumeration library. We then used
an existing bug benchmark suite to compare the bug finding
capabilities of the original, ad hoc random generator to
generators based on fair and unfair enumeration
combinators. The enumeration using the fair combinators has
complementary strengths to the ad hoc generator (better on
short time scales and worse on long time scales) and using
unfair combinators is worse across the board.
}

@include-section["intro.scrbl"]

@include-section["combinators.scrbl"]

@include-section["fair-informal.scrbl"]

@include-section["fair-formal.scrbl"]

@;; comment this out for now because it causes problems at the latex somehow
@;@include-section["redex-enumeration.scrbl"]

@include-section["evaluation.scrbl"]

@include-section["related.scrbl"]

@include-section["future.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

