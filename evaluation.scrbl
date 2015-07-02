#lang scribble/base

@(require "cite.rkt"
          "util.rkt"
          "results/plot-lines.rkt"
          "results/plot-points.rkt"
          scribble/manual
          scriblib/figure
          scriblib/footnote
          racket/runtime-path
          racket/set racket/list
          (only-in pict scale))

@title[#:tag "sec:evaluation"]{Empirical Evaluation}

As the primary motivation for studying enumerations is test
case generation, we performed an empirical evaluation of
fair and unfair enumerations to try to understand the impact
of using unfair combinators on test case generation. We also
used a mature ad hoc random generator as a baseline for the
comparison, to give our results some context. This section
describes the setup of our evaluation and its results.

@section{Setup}

We conducted the evaluation in the context of
Redex@~cite[redex-rta redex-book], a domain-specific programming language
for operational semantics, type systems, and their
associated machinery. Redex gives semantics engineers the
ability to formulate and check claims about their semantics
and it includes a random test case generator that can be
used to automatically falsify such claims.

Our evaluation used the Redex benchmark, which consists of
a number of models, including the Racket virtual machine
model@~cite[racket-virtual-machine], a polymorphic
λ-calculus used for random testing in other work 
@~cite[palka-workshop generating-random-lambda-terms], the
list machine benchmark@~cite[list-machine], and a delimited
continuation contract model@~cite[delim-cont-cont], as well
as a few models we built ourselves based on our experience
with random generation and to cover typical Redex
models.@note{The full benchmark is online:
 @url{http://docs.racket-lang.org/redex/benchmark.html}}
Each model comes with a number of variations, each with a
different bug. Each model and bug pair is equipped with a
property that should hold for every term, but does not, due
to the bug. There are 8 models and 50 bugs in total.

The Redex benchmark comes equipped with a mechanism to add
new generators to each model and bug pair, as well as a
built-in ad hoc, random generator. We used the enumeration
library described in @secref["sec:enum"] to build two
generators based on enumeration, one that just chooses
terms in the order induced by the natural numbers,
and one that selects a random natural and uses that
to index into the enumeration.

The ad hoc random generation is Redex's existing random
generator@~cite[sfp2009-kf]. It has been tuned based on
experience programming in Redex, but not recently. From the
git logs, the most recent change to it was a bug fix in
April of 2011 and the most recent change that affected the
generation of random terms was in January of 2011, both well
before we started studying enumeration.

The ad hoc random generator, which is based on the method of
recursively unfolding non-terminals, is parameterized over
the depth at which it attempts to stop unfolding
non-terminals. We chose a value of 5 for this depth since
that seemed to be the most successful. This produces terms
of a similar size to those of the random enumeration method,
although the distribution is different.

For the random selection from an enumeration, we
need a mechanism to pick a natural number. To do this, we
first pick an exponent @texmath{i} in base 2 from the
geometric distribution and then pick uniformly at random an
integer that is between @texmath{2^{i-1}} and 
@texmath{2^i}. We repeat this process three times
and then take the largest -- this helps make
sure that the numbers are not always small.

@figure*["fig:benchmark-lines"
         @list{Overview of random testing performance of ad hoc generation,
               in-order enumeration, and random indexing into an enumeration,
               on a benchmark of Redex models.}
         (plot-lines-from-directory)]

We chose this distribution because it does not have a fixed
mean. That is, if you take the mean of some number of
samples and then add more samples and take the mean again,
the mean of the new numbers is likely to be larger than from
the mean of the old sample. We believe this is a good
property to have when indexing into our enumerations so as
to avoid biasing our indices towards a small size.

The random-selection results are sensitive to the
probability of picking the zero exponent from the geometric
distribution. Because this method was our
worst performing method, we empirically chose
benchmark-specific numbers in an attempt to maximize the
success of the random enumeration method. Even with
this artificial help, this method was still worse, overall,
than the other two.

@figure*["fig:benchmark-overview"
         @list{The mean time each generator takes to find the bugs,
               for each bug that some generator found; bars indicate
               90% confidence intervals}
         (plot-points-from-directory)]

We used three variations on the enumeration combinators. The
first is the fair combinators described in 
@secref["sec:fair-informal"]. The second uses fair binary
pairing and binary alternation combinators, but that are
unfairly generalized via nesting (to create n-tuples or
n-way alternations), which we call ``mildly unfair''.
The third variation uses the unfair binary pairing
combinator based on the bijection described in the
introduction, also unfairly generalized to n-ary pairing. It
uses an analogous unfair alternation combinator that goes
exponentially deep into one argument as compared to the
other, also unfairly generalized to n-ary alternation.
The final one we call ``brutally unfair''.

For each of the 350 bug and generator combinations, we
run a script that repeatedly asks for terms and checks to
see if they falsify the property. As soon as it finds a
counterexample to the property, it reports the amount of
time it has been running. The script runs until the
uncertainty in the average becomes acceptably small or until
24 hours elapses, whichever comes first. In a second pass,
we re-ran the bug/generator combinations where at least one
counterexample was found, but where the uncertainty in the
average will still large. We let each of these combinations
run for a week of CPU time.

We used two identical 64 core AMD machines with Opteron
6274s running at 2,200 MHz with a 2 MB L2 cache to run the
benchmarks. Each machine has 64 gigabytes of memory. Our
script typically runs each model/bug combination
sequentially, although we ran multiple different
combinations in parallel and, for the bugs
that ran for more than 24 hours, we ran tests in parallel. We
used version 6.2.0.4 (from git on June 7, 2015) of Racket,
of which Redex is a part.

@section{Results}

The plots in @figure-ref["fig:benchmark-lines"] show a
high-level view of our results. Along x-axis is time in
seconds in a log scale, varying from milliseconds to the
left to a few hours on the right. Along the y-axis is the
total number of counterexamples found for each point in
time. The lines on each plot show how the number of
counterexamples found changes as time passes.

The thicker, black line is the same on both plots. It shows
the number of counter examples found by the ad hoc random
generator. The upper plot shows how drawing from the
enumeration in order fares, compared to the random
generator. The solid red (not thick) line is with fair
combinators, the dashed line is with the mildly unfair
combinators and the dotted line is with the brutally unfair
combinators. Similarly, the bottom plot uses the same set of
combinators, but randomly picks natural numbers (as
described above) and uses those to generate candidates.
No strategy was able to find more than
@(format "~a" (maximum-bugs-found)) of the 50 bugs in the benchmark.

As the plots show, the mildly unfair combinators are worse
than the fair ones and the brutally unfair combinators are
much worse.

A more detailed version of our results is shown in 
@figure-ref["fig:benchmark-overview"]. The x-axis has one
entry for each different bug, for which a counter-example
was found. Each point indicates the average number of seconds
required to find that bug, with the bars indicating a 95%
confidence interval. The different shapes and colors of the points
indicate which method was used. The bugs are sorted along
the x-axis by the average amount of time required to find
the bug across all strategies.

@Figure-ref["fig:benchmark-overview"]'s chart confirms the
conclusion from @figure-ref["fig:benchmark-lines"]'s.
Specifically, the circled points are the ones with unfair
combinators and they are never significantly below their
uncircled counterparts and often significantly above.

@(define wb (way-betters))
@(assert (equal? (set 'ordered 'grammar)
                 (apply set (hash-keys wb))))
@(define (betters who)
   (define with-commas (add-between (sort (hash-ref wb who) string<?) ", "))
   (assert (> (length with-commas) 2))
   (define last-one (last with-commas))
   (define with-and (reverse (list* last-one ", and " (cddr (reverse with-commas)))))
   (assert (= (length with-and) (length with-commas)))
   (apply string-append with-and))

@Figure-ref["fig:benchmark-overview"] also shows that, for
the most part, bugs that were easy (could be found in less
than a few seconds) for the
generator that selected at random from the enumerations
were easy for all three generators.
The ad hoc random generator and the fair in-order enumeration
generator each had a number of bugs where they were at least
one decimal order of magnitude faster than all of the other
generators (and multiple generators found the bug).
The ad hoc random generator was significantly better on:
@(betters 'grammar),
and the fair in-order enumerator was significantly better on:
@(betters 'ordered). The unfair enumerators were never significantly
better on any bug.

