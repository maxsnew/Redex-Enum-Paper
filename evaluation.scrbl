#lang scribble/base

@(require "cite.rkt"
          "util.rkt"
          "results/plot-lines.rkt"
          "results/plot-points.rkt"
          scribble/manual
          scriblib/figure
          scriblib/footnote
          racket/runtime-path
          (only-in pict scale))

@(define-runtime-path 10-17-14 "results/10-17-14")

@title[#:tag "sec:evaluation"]{Empirical Evaluation}

We compared three types of test-case generation using a set
of buggy models. Each model and bug is equipped with a
property that should hold for every term (but does not, due to
the bug) and three functions that generate terms, each with
a different strategy: in-order enumeration, random selection
from a uniform distribution, and ad hoc random generation.
The full benchmark consists of a number of models, including
the Racket virtual machine model@~cite[racket-virtual-machine],
a polymorphic λ-calculus used for random testing in other 
work@~cite[palka-workshop generating-random-lambda-terms], the list machine 
benchmark@~cite[list-machine], and a delimited continuation 
contract model@~cite[delim-cont-cont], as well as a few models
we built ourselves based on our experience with random generation
and to cover typical Redex 
models.@note{The full benchmark is online: @url{http://docs.racket-lang.org/redex/benchmark.html}}

For each bug and generator, we run a script that repeatedly
asks for terms and checks to see if they falsify the property.
As soon as it finds a counterexample to the property, it reports
the amount of time it has been running. The script runs until
the uncertainty in the average becomes acceptably small or
until 24 hours elapses, whichever comes first.

@figure*["fig:benchmark-lines"
         @list{Overview of random testing performance of ad hoc generation,
               enumeration, and random indexing into an enumeration,
               on a benchmark of Redex models.}
         (plot-lines-from-directory 10-17-14)]

We used two identical 64 core AMD machines with Opteron
6274s running at 2,200 MHz with a 2 MB L2 cache to run the
benchmarks. Each machine has 64 gigabytes of memory. Our script
runs each model/bug combination sequentially, although we
ran multiple different combinations at once in parallel.
We used the unreleased version 6.1.1.1 of Racket (of which
Redex is a part); more precisely the version at git commit
@tt{878358ec9e}.@note{@url{https://github.com/plt/racket/commit/878358ec9e2}}

For the in-order enumeration, we simply indexed into the
decode functions (as described in @secref["sec:enum"]),
starting at zero and incrementing by one each time. 

For the random selection from the uniform distribution, we
need a mechanism to pick a natural number. To do this, we
first pick an exponent @raw-latex|{$i$}| in base 2 from the
geometric distribution and then pick uniformly at random an
integer that is between @raw-latex|{$2^{i-1}$}| and 
@raw-latex|{$2^i$}|. We repeat this process three times
and then take the largest -- this helps make
sure that the numbers are not always small.

We choose this distribution because it does not have a fixed mean.
That is, if you take the mean of some number of samples and
then add more samples and take the mean again, the mean of
the new numbers is larger than from the mean of the old. We
believe this is a good property to have when indexing into
our uniform distribution so as to avoid biasing our indices
towards a small size.

The random-selection results are quite sensitive to the
probability of picking the zero exponent from the geometric
distribution. Because this method was our
worst performing method, we empirically chose
benchmark-specific numbers in an attempt to maximize the
success of the random uniform distribution method. Even with
this artificial help, this method was still worse, overall
than the other two.

@figure*["fig:benchmark-overview"
         @list{The mean time each generator takes to find the bugs,
               for each bug that some generator found; bars indicate
               90% confidence intervals}
         (plot-points-from-directory 10-17-14)]

For the ad hoc random generation, we use Redex's existing 
random generator@~cite[sfp2009-kf]. It has been tuned
based on our experience programming in Redex, but not
recently. The most recent change to it was a bug fix in
April of 2011 and the most recent change that affected
the generation of random terms was in January of 2011,
both well before we started working on the enumerator. 

This generator, which is based on the method of recursively
unfolding non-terminals, is parameterized over the depth at
which it attempts to stop unfolding non-terminals. We chose
a value of 5 for this depth since that seemed to be the
most successful. This produces terms of a similar size to
those of the uniform random generator, although the
distribution is different.

@Figure-ref["fig:benchmark-lines"] shows a high-level view
of our results. Along its x-axis is time in seconds in a log
scale, and along the y-axis is the total number of counterexamples
found for each point in time. There are three lines on the
plot showing how the total number of counterexamples found changes as
time passes.

The red dashed line shows the performance of in-order
enumeration and it is clearly the winner in the left-hand
side of the graph. The solid black line shows the performance
of the ad hoc random generator and it is clearly the winner
on the right-hand side of the graph, i.e. the longer
time-frames.

There are two crossover points marked on the graph with
black dots. After 2 minutes, with 22 of the bugs found, the
enumerator starts to lose and random selection from the
uniform distribution starts to win until 3 minutes pass, at
which time the ad hoc generator starts to win and it never
gives up the lead.

Overall, we take this to mean that on interactive
time-frames, the in-order enumeration is the best method and
on longer time-frames ad hoc generation is the best. While
selection from the uniform distribution does win briefly, it
does not hold its lead for long and there are no bugs that
it finds that ad hoc generation does not also find.

Although there are 50 bugs in the benchmark, no strategy was
able to find more than 37 of them in a 24 hour period.

@Figure-ref["fig:benchmark-overview"] also shows that, for
the most part, bugs that were easy (could be found in less
than a few seconds) for either the ad hoc generator or the
generator that selected at random from the uniform
distribution were easy for all three generators. The
in-order enumeration, however, was able to find several bugs
(such as bug #8 in poly-stlc and #7 in let-poly) in much
shorter times than the other approaches.

