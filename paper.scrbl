#lang scribble/lncs

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
                 
                 ;; used for the table of the bugs
                 #"\\newcommand{\\ErrorDescriptionBox}[1]{"
                 #"\\begin{minipage}[t]{4in}#1\\end{minipage}}"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  Practical, Fair, and Efficient Enumeration for Algebraic Data-Structures
}
@authors[(author #:inst "1" "Max New")
         (author #:inst "1" "Burke Fetscher")
         (author #:inst "2" "Jay McCarthy" )
         (author #:inst "1" "Robert Bruce Findler")]
@institutes[(institute "Northwestern University")
            (institute "Vassar College")]

@abstract{
 This paper reports on the design of a set of
 enumeration combinators that are efficient, fair, 
 and practical. They are efficient because most
 of the combinators produce enumerations that
 support indexing in time proportional to the
 log of the given index. In practical terms, this
 means that we can typically compute the 
 @raw-latex{$2^{100,000}$}th element of an enumeration 
 in a few milliseconds.
 
 Fairness means that when the combinators build a new result
 enumeration out of other ones, indexing into the result enumerator
 does not index disproportionally
 far into just a subset of the given enumerators. For example, 
 this means that enumeration of the
 @raw-latex{$n$}th element of a product
 indexes about @raw-latex{$\sqrt{n}$} elements into each
 of its components.
 
 Our combinators are practical because they support the
 entire language of Redex models, providing a new generator
 for Redex's property-based testing. The paper reports
 on an empirical comparison between enumeration-based 
 property generation and ad hoc random generation, showing
 that enumeration is more effective than ad hoc random
 generation in short time-frames.
}

@include-section["combinators.scrbl"]

@include-section["fairness.scrbl"]

@include-section["redex-enumeration.scrbl"]

@include-section["methodology.scrbl"]

@include-section["results.scrbl"]

@include-section["related.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

