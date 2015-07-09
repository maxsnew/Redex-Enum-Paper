#lang scribble/base
@(require scribble/core)

@title[#:tag "sec:conclusion"]{Conclusion}

This paper presents a new concept for enumeration libraries that
we call @emph{fairness}, backing it up with a theoretical development
of fair combinators, an implementation, and an empirical
study showing that fair enumeration can support an 
effective testing tool and that unfair enumerations cannot.

Indeed, the results of our empirical study have convinced us
to modify Redex's default random testing functionality. The new
default strategy for random testing first tests a property
using the in-order enumeration for 10 seconds, then
alternates between enumeration and the ad hoc random
generator for 10 minutes, then finally switches over to just
random generation. This provides users with the
complementary benefits of in-order and random enumeration as
shown in our results, without the need for any
configuration.

@;{
 @(element (style "paragraph" '()) '("Acknowledgments."))

Thanks to Neil Toronto for helping
us find a way to select from the natural numbers at random.
Thanks to Ben Lerner for proving a square root property that gave us
fits.
Thanks to Hai Zhou, Li Li, Yuankai Chen, and Peng Kang for
graciously sharing their compute servers with us. Thanks to
William H. Temps, Matthias Felleisen, and Ben Greenman for helpful comments on the writing.
Thanks to one of the anonymous reviewers at ICFP 2015 for suggesting
that we refine our definition of fairness with a function.
}

@(element (style "newpage" '()) '())
