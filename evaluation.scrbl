#lang scribble/base

@(require "cite.rkt"
          "util.rkt"
          "results/plot-lines.rkt"
          "results/plot-points.rkt"
          "results/plot-rates.rkt"
          scribble/manual
          scriblib/figure
          scriblib/footnote
          racket/runtime-path
          racket/set racket/list
          (only-in pict scale))

@title[#:tag "sec:evaluation"]{Empirical Evaluation}

As our motivation for studying enumerations is test case
generation, we performed an empirical evaluation of fair and
unfair enumerations described earlier in the paper to try to
understand the impact of using unfair combinators on test
case generation. We also used a mature ad hoc random
generator as a baseline for the comparison, to give our
results some context. This section describes our evaluation
and its results.

@section{Setup}

We conducted the evaluation in the context of
Redex@~cite[redex-rta redex-book], a domain-specific language
for operational semantics, type systems, and their
associated machinery. Redex gives semantics engineers the
ability to formulate and check claims about their semantics
and it includes a random test case generator that can be
used to automatically falsify such claims.

Our evaluation used the Redex benchmark, which consists of
a number of models, including the Racket virtual machine
model@~cite[racket-virtual-machine], a polymorphic
λ-calculus used for random testing@~cite[palka-workshop generating-random-lambda-terms],
the list machine benchmark@~cite[list-machine], and a delimited
continuation contract model@~cite[delim-cont-cont], as well
as a few models we built ourselves based on our experience
with random generation and to cover typical Redex
models.@note{It is online:
 @url{https://docs.racket-lang.org/redex/benchmark.html}}
Each model comes with a number of buggy variations.
Each model and bug pair is equipped with a
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
generator@~cite[sfp2009-kf]. It generates expressions
matching a particular non-terminal by randomly choosing
a production, expanding the non-terminal based on the production
chosen, and then repeating the process until a depth bound
is reached. At that point, it limits the random choice to
productions that do not require recursive unfoldings (such
productions are guaranteed to exist or else the original Redex
program would have been syntactically ill-formed).

It has been tuned based on experience programming in Redex,
but not recently. From the git logs, the most recent change
to it was a bug fix in April of 2011 and the most recent
change that affected the generation of random terms was in
January of 2011, both well before we started studying
enumeration.

For our evaluation, we use the default value of 5 for this
depth since that is what Redex users see without
customization. This produces terms of a similar size to
those of the random enumeration method (although the
distribution is different).

To pick a random natural number to index into the enumeration, we
first pick an exponent @texmath{i} in base 2 from the
geometric distribution and then pick uniformly at random an
integer that is between @texmath{2^{i-1}} and 
@texmath{2^i}. We repeat this process three times
and then take the largest -- this helps make
sure that the numbers are not always small.

@figure["fig:dominates"
        @list{Partial Order Between Generators Indicating Which Find More Bugs}
        @raw-latex{\includegraphics[scale=.6]{dominates.pdf}}]

@figure*["fig:benchmark-ordered-lines"
         @list{Overview of random testing performance of ad hoc generation
               and in-order enumeration}
         (plot-ordered-lines-from-directory)]

@figure*["fig:benchmark-enum-lines"
         @list{Overview of random testing performance of ad hoc generation
               and random indexing into an enumeration}
         (plot-enum-lines-from-directory)]

@figure*["fig:benchmark-points"
         @list{Time taken to find each bug for each generator}
         (plot-points-from-directory)]

We chose this distribution because it does not have a fixed
mean. That is, if you take the mean of some number of
samples and then add more samples and take the mean again,
the mean of the new numbers is likely to be larger than
the mean of the old. We believe this is a good
property to have when indexing into our enumerations so
we avoid biasing our indices towards a small size.

The random-selection results are sensitive to the
probability of picking the zero exponent from the geometric
distribution. Because this method was our
worst performing method, we empirically chose
benchmark-specific numbers in an attempt to maximize the
success of the random enumeration method. Even with
this artificial help, this method was still worse, overall,
than the others.

We used three variations on the enumeration combinators. The
first is the fair combinators described in 
@secref["sec:fair-informal"]. The second uses fair binary
pairing and binary alternation combinators, but that are
unfairly generalized via nesting (to create @texmath{n}-tuples or
@texmath{n}-way alternations), which we call ``mildly unfair''.
The third variation uses the unfair binary pairing
combinator based on the bijection described in the
introduction, also unfairly generalized to @texmath{n}-ary pairing. It
uses an analogous unfair alternation combinator that goes
exponentially deep into one argument as compared to the
other, also unfairly generalized to @texmath{n}-ary alternation.
The final one we call ``brutally unfair''.

For each of the 350 bug and generator combinations, we run a
script that repeatedly asks for terms and checks to see if
they falsify the property. As soon as it finds a
counterexample to the property, it reports the amount of
time it has been running. We ran the script in two rounds.
The first round ran all 350 bug and generator combinations
until either 24 hours elapsed or the standard error in the
average became less than 10% of the average. Then
we took all of the bugs where the 95% confidence interval
was greater than 50% of the average and where at least one
counterexample was found and ran each of those for an
additional 8 days. All of the final averages have
an 95% confidence interval that is less than 50% of the average.

@figure*["fig:rates"
         @list{Examples tested per second for each benchmark model and enumeration-based generator}
         (rate-plots)]


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

The graph in @figure-ref["fig:dominates"] gives a high-level
view of which generators are more effective at finding bugs.
There is an edge between two generators if the one above
finds all the bugs that the one below finds and the one below
was unable to find at least one bug that the one above
found. By this metric, the ad hoc random generator is a
clear winner, the fair enumerators are second and the
unfair ones are third, with the mildly unfair enumerators
usually doing better than the brutally unfair ones.

That overview lacks nuance; it does not
take into account how long it took for each generator to find
the bugs that it found. 
The plot in @figure-ref["fig:benchmark-ordered-lines"] take time
into account, showing how well each generator is doing as
a function of time. Along x axis is time in
seconds in a log scale, varying from milliseconds to
a few hours. Along the y axis is the
total number of counterexamples found for each point in
time. The lines on each plot show how the number of
counterexamples found changes as time passes.

The thicker, black line shows
the number of counterexamples found by the ad hoc random
generator. The solid red (not thick) line is with fair
combinators, the dashed line is with the mildly unfair
combinators and the dotted line is with the brutally unfair
combinators, all when running in order.
This plot shows that the mildly unfair combinators are worse
than the fair ones and the brutally unfair combinators are
much worse than either.

That plot also reveals that the ad hoc generator is only better than
the best enumeration strategy after 3 minutes.  Before that time, the
fair in-order enumeration strategy is the best approach.

@Figure-ref["fig:benchmark-enum-lines"]
has a similar plot that uses the
same set of combinators, but randomly picks natural numbers
(as described above) and uses those to generate candidates.
This plots shows that that approach is never the best approach, on
any time scale.

No strategy was able to find more than
@(format "~a" (maximum-bugs-found)) of the 50 bugs in the
benchmark. 

@Figure-ref["fig:benchmark-points"] shows a plot of every
generator's performance on each bug.
The x axis has one entry for each different bug (for which a counter-example
was found) and the y axis shows the average number of seconds
required to find that bug. The chart confirms the
conclusion from @figure-ref["fig:benchmark-ordered-lines"] showing that
the unfair combinators are never significantly below their
fair counterparts and often significantly above.

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
@(define (better-count who)
   (format "~a" (length (hash-ref wb who))))

Our data also shows that, for
the most part, bugs that were easy (could be found in less
than a few seconds) for the
generator that selected at random from the enumerations
were easy for all three generators.
The ad hoc random generator and the fair in-order enumeration
generator each had a number of bugs where they were at least
one decimal order of magnitude faster than all of the other
generators (and multiple generators found the bug).
The ad hoc random generator was significantly better on
@(better-count 'grammar) bugs
and the fair in-order enumerator was significantly better on
@(if (equal? (better-count 'ordered) (better-count 'grammar))
     "(a different)"
     "")
@(better-count 'ordered) bugs. The unfair enumerators were never significantly
better on any bug.

We believe the reason that the fair enumerators are better than the unfair
ones is that their more balanced exploration of the space leads
to a wider variety of interesting examples being tested.
@Figure-ref["fig:rates"] provides some evidence for this theory.
It shows the number of examples tested per second for each model
(the Redex bug benchmark does not cause our generators or the ad hoc
random generator to generate different per-bug examples, only different per-model examples)
under the different generator strategies. The upper plot shows
the in-order generators and the lower plot shows the generators
that selected random natural numbers and used those to generate examples.
In every case, the fair enumeration strategy generates fewer
examples per second (except for the list-machine benchmark in
the random generator, where it is only slightly faster). And yet the
fair generators find more bugs. This suggests that the unfair generators
are repeatedly generating simple examples that can be tested
quickly, but that provide little new information about the model.
We believe this is because the unfair generators spend a lot of time exploring
programs that differ only in the names
of the variables or have other uninteresting variations.
