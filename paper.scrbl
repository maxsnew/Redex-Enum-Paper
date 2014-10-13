#lang scribble/lncs

@(require "cite.rkt" 
          scribble/core
          scribble/latex-properties)

@(define extra-tex-code
   (bytes-append #"\\usepackage{pslatex}\n"
                 #"\\usepackage{inconsolata}\n"
                 
                 ;; used for the table of the bugs
                 #"\\newcommand{\\ErrorDescriptionBox}[1]{"
                 #"\\begin{minipage}[t]{4in}#1\\end{minipage}}"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  An Empirical Comparison Between Random Generation and Enumeration
  for Testing Redex Models
}
@;{@doi{}}
@;{TODO: add e-mails, institutions}
@authors[@(author #:inst "1" "Max New")
         @(author #:inst "2" "Burke Fetscher")
         @(author #:inst "3" "Jay McCarthy")
         @(author #:inst "2" "Robert Bruce Findler")]
@institutes[@institute{Northeastern University}
            @institute{Northwestern University}
            @institute{Vassar College}]         

@abstract{ 
          
This paper presents a benchmark suite of buggy Redex models
designed to test bug-finding techniques. Our benchmark
contains large and small models, easy and hard to find bugs,
bugs that we invented based on our experience programming in
Redex and bugs in models written by others that happened
during development.
  
We evaluate three testing techniques: a generic, ad hoc
random generator tuned for Redex programs, random selection
from a uniform distribution of Redex programs, and an
in-order enumeration of Redex programs.
  
Our results show that selecting uniformly at random is
not the best-performing choice, and enumeration and ad hoc random
selection are incomparable, with random being better with
more than 10 minutes but in-order enumeration being better
in interactive time-frames.

}

@include-section["intro.scrbl"]

@include-section{combinators.scrbl}

@include-section{fairness.scrbl}

@include-section["redex-enumeration.scrbl"]

@include-section{methodology.scrbl}

@include-section{benchmark.scrbl}

@include-section{results.scrbl}

@include-section{related.scrbl}

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

