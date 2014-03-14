#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          scriblib/figure
          (only-in pict scale))

Our main motivation in developing enumerations for Redex patterns
is to improve Redex's automated testing capabilities by using
enumerations as test generators. 
To gain insight into the enumerator's
utility for random testing, we compared the performance of two 
enumeration-based strategies to Redex's preexisting random
test generator.
To do so, we developed a benchmark of buggy Redex models
that evaluates test case generators based on how quickly 
they are able to find bugs.

The preexisting random generator@~cite[sfp2009-kf] takes a pattern 
and a grammar as inputs and generates a random instance of the 
pattern by recursively unfolding non-terminals in the grammar, 
choosing randomly between productions.
This straightforward strategy has been an effective approach
based on past studies.@~cite[run-your-research]
We used the enumerator in two new test generation strategies,
both of which also take a pattern and a grammar as their inputs,
which are used to construct an enumeration of the possible
terms for that pattern.
The first enumeration-based strategy produces random terms
by simply choosing random indexes into the enumeration.
We hoped this approach would be an improvement over the baseline
Redex generator because it chooses terms uniformly, whereas the
baseline generator clearly does not.
For the second strategy, we used the enumerator to exhaustively
produce terms satisfying a pattern in enumerated order starting 
from 0.

Perhaps surprisingly, we found that the random enumeration-based
strategy had the worst performance. For easy to find bugs
(easy in the sense that at least one of the models was able to
find a counterexample quickly) the in-order enumeration performed
best, while for more difficult to find bugs the baseline strategy
of recursively unfolding non-terminals was still the most effective.

@section{Methodology}

The benchmark is based on six different Redex models, each
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



@figure["fig:benchmark-lines"
        @(list "Random testing performance of in-order enumeration, random indexing into an enumeration, "
               "and recursive generation from a grammar on a benchmark of Redex models.")
        (scale (line-plot-24hour) 0.75)]

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



@figure*["fig:benchmark"
         "Performance results by individual bug."
         (scale (res-plot-24hour) 0.75)]