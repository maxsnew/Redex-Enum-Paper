#lang scribble/sigplan

@(require "cite.rkt" 
          scribble/core
          scribble/latex-properties)

@(define extra-tex-code
   (bytes-append #"\\usepackage{pslatex}\n"
                 #"\\usepackage{inconsolata}\n"
                 
                 ;; used for the table of the bugs
                 #"\\newcommand{\\ErrorDescriptionBox}[1]{"
                 #"\\begin{minipage}[t]{4.5in}#1\\end{minipage}}"))

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

@abstract{
 This paper presents a benchmark suite 
 of buggy Redex models designed to test
 bug-finding techniques. Our benchmark
 contains large and small models,
 easy and hard to find bugs, bugs
 that we invented based on our experience
 programming in Redex and bugs in models
 written by others that happened during 
 development.
  
 We evaluate three testing techniques:
 a generic, yet tuned random generator for Redex
 programs, random selection from 
 a uniform distribution of Redex programs, and 
 an in-order enumeration of Redex programs.
  
 Our results contradict commonly-held, yet
 unsubstantiated wisdom regarding the relative value
 of these three approaches. 
 Specifically, selecting uniformly
 at random is the worst-performing choice,
 and enumeration and random selection 
 are incomparable, with random being better
 in the multi-hour long time frames, but in-order
 enumeration being better the in multi-minute
 time frames.
}

@include-section["intro.scrbl"]

@section[#:tag "sec:enum"]{Enumeration Combinators}
@include-section{combinators.scrbl}

@include-section["redex-enumeration.scrbl"]

@section{Methodology}
@include-section{methodology.scrbl}

@section{Bechmark Overview and Bug-Specific Results}
@include-section{benchmark.scrbl}

@section[#:tag "sec:results"]{Global Trends in Our Results}
@include-section{results.scrbl}

@section[#:tag "sec:related-work"]{Related Work}
@include-section{related.scrbl}

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

