#lang scribble/base

@(require ;; "results/plot.rkt"
          "cite.rkt"
          scriblib/figure
          (only-in pict scale))

@title[#:tag "sec:results"]{Global Trends in Our Results}
@;{
@figure*["fig:benchmark-lines"
         @list{Random testing performance of in-order enumeration, 
               random indexing into an enumeration,
               and recursive generation from a grammar on 
               a benchmark of Redex models.}
         (line-plot-24hour)]

@figure["fig:correlation"
         @list{Scatter Plot Between Human Estimate of Complexity and
               Random Generation Success Time in Seconds (Right-most column shows
               bugs whose counterexamples were never found)}
         (correlation-plot-24hour)]
}
Our primary concern with this study was to determine the
relative merits of the three generation strategies. 
@Figure-ref["fig:benchmark-lines"] shows our data with this
aim in mind. Along its x-axis is time in seconds, again with
a log scale, and along the y-axis is the total number of bugs
found for each point in time. There are three lines on the
plot showing how the total number of bugs found changes as
time passes.

The blue dashed line shows the performance of in-order
enumeration and it is clearly the winner in the left-hand
side of the graph. The solid red line shows the performance
of the ad hoc random generator and it is clearly the winner
on the right-hand side of the graph, i.e. the longer
time-frames.

There are two crossover points marked on the graph with
black dots. After 2 minutes, with 17 of the bugs found, the
enumerator starts to lose and random selection from the
uniform distribution starts to win until 7 minutes pass, at
which time the ad hoc generator starts to win and it never
gives up the lead.

Overall, we take this to mean that on interactive
time-frames, the in-order enumeration is the best method and
on longer time-frames ad hoc generation is the best. While
selection from the uniform distribution does win briefly, it
does not hold its lead for long and there are no bugs that
it finds that ad hoc generation does not also find.

Although there are 43 bugs in the benchmark, no strategy was
able to find more than 30 of them in a 24 hour period.

@Figure-ref["fig:benchmark-overview"] also shows that, for
the most part, bugs that were easy (could be found in less
than a few seconds) for either the ad hoc generator or the
generator that selected at random from the uniform
distribution were easy for all three generators. The
in-order enumeration, however, was able to find several bugs
(such as bug #8 in poly-stlc) in much shorter times than the
other approaches.

We also compared the human notion of complexity of the bugs
to how well the three random generators do, using the
scatter plots in @figure-ref["fig:correlation"]. The x-axis
shows the amount of time that a given generator took to find
the bug and y-axis has the human-ranked complexity of the
bug. For bugs that were never found, a single black dot
(along with the count of bugs) is placed in a column on the
right-hand side of the graph. These plots show that there is
no correlation between how humans view the importance of the
bugs and how effective our generators are at finding it.
