#lang scribble/base

@(require "results/plot.rkt"
          scriblib/figure)

@section{Methodology}

The benchmark is baed on six different Redex models, each
of which consists of a grammar, a dynamic semantics, and some
static well-formedness property. (The last is usually a type system.)
Each has some predicate that relates the dynamic
properties of the system to the static properties, such
as type soundness.

For each model, several ``mutations'' provide the tests for the benchmark.
The mutations are made by manually introducing bugs into a copy 
of the model, such that each mutation is identical to the correct
version aside from a single bug.

Given a method of producing random terms, the benchmark repeatedly
attempts to find a counterexample for a buggy model by generating
a term and checking it with the model's correctness property.
Our performance metric is the average interval between counterexamples 
(or, for deterministic generators, the interval before the 
first counterexample is found).


@figure*["fig:benchmark"
         @(list "Random testing performance of in-order enumeration, random indexing into an enumeration, "
                "and recursive generation from a grammar on a benchmark of Redex models.")
         (res-plot-4hour)]

@section{Results}

@; TODO: expand once final results are in

@Figure-ref["fig:benchmark"] shows the random test performance results
for the three generation methods. 
The average interval between counterexamples is shown with a logarithmic
scale on the y-axis, and each column along the x-axis represents a single
bug. The points plotted with circles represent averages for terms
generated recursively from the grammar, and those plotted with stars
and diamonds represent, respectively, averages for selecting randomly 
from enumerated terms and searching through an enumeration in order.
The error bars represent 95% confidence intervals in the averages. 
(The in-order enumeration method is deterministic and thus has no 
uncertainty.)

If a column lacks a point of some type, that means no counterexamples
were generated for that bug over the entire period for which we
ran the benchmark. 
Although there are 32 bugs in the benchmark, there
are only 19 bugs plotted, since none of the random generation methods
used here were able to find a counterexample for 13 of the bugs we
tested.

The averages shown in @figure-ref["fig:benchmark"] span nearly six
orders of magnitude from less than a tenth of a second to several hours
and thus represent a wide range of bugs in terms of how difficult it
was to generate counterexamples.

The most successful approach remained the baseline Redex generator.
@; say something here about ``fair'' distributions, need some cites
