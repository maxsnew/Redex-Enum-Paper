#lang scribble/base

@(require "results/plot.rkt"
          scriblib/figure)

@section{Methodology}

@section{Results}

@figure*["fig:benchmark"
         @(list "Random testing performance of in-order enumeration, random indexing into an enumeration, "
                "and recursive generation from a grammar on a benchmark of Redex models.")
         (res-plot-4hour)]