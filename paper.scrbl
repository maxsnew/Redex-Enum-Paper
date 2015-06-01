#lang scribble/sigplan

@(require "cite.rkt" 
          "util.rkt"
          "bad-nn-to-n.rkt"
          scribble/core
          scribble/latex-properties
          scriblib/footnote
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

@section{Introduction}

In the past few years a number of different libraries have
appeared that provide generic ways to build bijections
between data structures and the natural numbers. First was
Feat for Haskell in
2012@note{https://hackage.haskell.org/package/testing-feat},
then SciFe for Scala in
2014@note{http://kaptoxic.github.io/SciFe/}, and
@tt{data/enumerate} for Racket this
year.@note{http://plt.eecs.northwestern.edu/snapshots/current/doc/data/Enumerations.html}

These libraries are all efficient, generally providing the
ability to extract the @texmath{2^{100}}-th element of the
enumerations of data structures in milliseconds. What they
lack, however, is a mathematically precise notion of the
quality of their enumerations. As an example, all of
these libraries provide a pairing combinator that accepts
two enumerations and returns an enumeration of pairs of the
elements of the given enumeration. There are many ways one
might build such an enumeration, based on the many ways that
one might write a bijection between the natural numbers and
pairs of natural numbers. One such function is given by 
@texmath[bad-nn->n-string]. This is a bijection (the inverse
simply counts the number of times that two is a factor of the
input to separate the ``x'' and ``y'' parts) that is easy to
explain and efficient to compute in both directions. It is
a poor choice for an enumeration library, however, because it will
explore ``y'' coordinate values much more quickly
than the ``x'' coordinate. Indeed, in the first
@(add-commas bad-howmany) pairs, the biggest ``x'' coordinate
seen is @(add-commas bad-max-x) and the biggest ``y'' coordinate
seen is @(add-commas bad-max-y).

In this paper, we offer a criterion called @emph{fairness}
that classifies enumeration combinators. Intuitively, a
combinator is fair if indexing deeply into the result of the
combinator goes equally deeply into all the arguments to the
combinator. Our definition rules out a pairing operation
based on the function above, but accepts one based on the
standard Cantor bijection and many others, including ones
whose inverses are easier to compute in n-tuple case (as
explained later).

We also report on an empirical study of the bug-finding
capabilities of enumeration libraries for bugs in formal
models of type systems and operational semantics. We built a
benchmark suite of 50 bugs (based on our experience writing
Redex models and the experience of others mined from git
repositories of Redex models) and compare the bugs/second
rate for a generator that enumerates terms in order, one
that randomly selects a natural number and uses that to find
a term and an existing, ad hoc random generator that's been
tuned for bug-finding in Redex models for more than a
decade. Our results show that in-order enumeration and ad
hoc generation have complementary strengths, but that
selecting a random natural and using it with an enumeration
is almost always worse than one of the other two choices.

The next section introduces enumeration libraries, focusing
on the Racket-based library to make the introduction
concrete. Then, in @secref["sec:fair-informal"] we give an
intuition-based definition of fairness and follow up in 
@secref["sec:fair-formal"] with a formal definition. Our
evaluation of the different random generation strategies is
discussed in @secref["sec:evaluation"], and the last two
sections discuss related work and conclude.

@include-section["combinators.scrbl"]

@include-section["fair-informal.scrbl"]

@include-section["fair-formal.scrbl"]

@;; comment this out for now because it causes problems at the latex somehow
@;@include-section["redex-enumeration.scrbl"]

@include-section["evaluation.scrbl"]

@include-section["related.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

