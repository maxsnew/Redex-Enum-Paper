#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          scriblib/figure
          (only-in pict scale))

@figure["fig:benchmark-lines"
        @(list "Random testing performance of in-order enumeration, random indexing into an enumeration, "
               "and recursive generation from a grammar on a benchmark of Redex models.")
        (scale (line-plot-24hour) 0.75)]

@; TODO: expand once final results are in

Perhaps surprisingly, we found that the random enumeration-based
strategy had the worst performance. For easy to find bugs
(easy in the sense that at least one of the models was able to
find a counterexample quickly) the in-order enumeration performed
best, while for more difficult to find bugs the baseline strategy
of recursively unfolding non-terminals was still the most effective.

@Figure-ref["fig:benchmark-lines"] summarizes the testing performance 
results for the three generation methods. 
The x-axis show seconds on a logarithmic scale, and the y-axis shows 
the total number of bugs found in intervals less than a given time 
on the x-axis, so the plot shows how many of the bugs one would 
expect to find by running one of the generators for a fixed interval.
(The intervals are averages for random the generators,
and are the exact amount of time elapsed before the first counterexample is
found for the deterministic, in-order, method.) 
Strategies with better performance over a given interval will
lie to the left or above others for that interval.

Interestingly, @figure-ref["fig:benchmark-lines"] clearly shows that
the in-order enumeration is the best approach to use for time 
periods less than around ten seconds, after which it is quickly surpassed
by the other two strategies. For longer time periods, the baseline Redex
generator performs best. Choosing randomly from the enumeration is
never the best approach.

The data shown in @Figure-ref["fig:benchmark-lines"] represents running
each generation method on each bug for either 24 hours or until the error 
in the average interval was reasonably small. Although there are 32 bugs 
in the benchmark, no strategy was able to find more that 21 of them in
a 24 hour period.

@Figure-ref["fig:benchmark"] shows the results in more detail, with
the measured averages for each strategy on each bug displayed along
with uncertainties.
The error bars represent 95% confidence intervals in the averages. 
(The in-order enumeration method is deterministic and thus has no 
uncertainty.)

The averages shown in @figure-ref["fig:benchmark"] span nearly six
orders of magnitude from less than a tenth of a second to several hours
and thus represent a wide range of bugs in terms of how difficult it
was to generate counterexamples.

The most successful approach remained the baseline Redex generator.
@; say something here about ``fair'' distributions, need some cites



@figure*["fig:benchmark"
         "Performance results by individual bug."
         (scale (res-plot-24hour) 0.75)]

- explains

- in-order looks good for short time frames
- random gen better long
- sampling from enumeration never great

- nothing in upper left
- uncertanties
- some bugs hard for all of them
- easy bugs are easy for all of them
- some mixed

- blank spots on summary graph