#lang scribble/base
@(require scribble/core)

@title[#:tag "sec:conclusion"]{Conclusion}

Our study shows that the relationship between ad hoc random
generation and in-order enumeration is subtle, and that
selecting randomly from a uniform distribution is not as
effective for testing as it might appear.

Based on these findings we have modified Redex's random
testing functionality. The new default strategy for random
testing first tests a property using the in-order
enumeration for 10 seconds, then alternates between
enumeration and the ad hoc random generator for 10 minutes,
then finally switches over to just random generation. This will
provide users with the complementary benefits of in-order
and random enumeration as shown in our results without the
need for manual configuration.

@(element (style "paragraph" '()) '("Acknowledgements."))
Thanks to Neil Toronto for helping
us find a way to select from the natural numbers at random.
Thanks to Hai Zhou, Li Li, Yuankai Chen, and Peng Kang for
graciously sharing their compute servers with us. Thanks to
Matthias Felleisen for helpful comments on the writing. 
