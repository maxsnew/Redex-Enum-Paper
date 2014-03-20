#lang scribble/sigplan

@(require "cite.rkt" 
          scribble/core
          scribble/latex-properties)

@(define extra-tex-code #"\\usepackage{inconsolata}\n")

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  An Empirical Comparison Between Random Generation and Enumeration
  for Testing Redex Models
}
@doi{}

@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]
@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]
@authorinfo["Jay McCarthy"
            "Brigham Young University"
            "jay@cs.byu.edu"]
@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]

@section{Introduction}

Enumeration! Whoo hoo!

@section{Enumeration Combinators}
@include-section{combinators.scrbl}

@section{Enumerating Redex Patterns}

@section{Evaluation}
@include-section{evaluation.scrbl}

@section{Related Work}
@include-section{related.scrbl}

@section{Conclusion}

@generate-bibliography[]
