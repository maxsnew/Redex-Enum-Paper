#lang scribble/base
@(require scribble/core)

@title[#:tag "sec:conclusion"]{Conclusion}

Our study shows that the relationship between ad hoc random
generation and in-order enumeration is subtle, and that
selecting randomly from a uniform distribution is not as
effective for testing as the literature claims. 

We have also learned that random testing's successes and
failures are hard to predict. For example, why is stlc bug
#4 so much harder to find than stlc bug #8? They both
mistake the type int for some non-integer and have similarly
small counter examples.

@(element (style "paragraph" '()) '("Acknowledgements."))
Thanks to Neil Toronto for helping
us find a way to select from the natural numbers at random.
Thanks to Hai Zhou, Li Li, Yuankai Chen, and Peng Kang for
graciously sharing their compute servers with us. Thanks to
Matthias Felleisen for helpful comments on the writing. 
