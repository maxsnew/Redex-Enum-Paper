#lang scribble/sigplan @10pt

@(require "cite.rkt" 
          scribble/core
          scribble/latex-properties)

@(define extra-tex-code
   (bytes-append #"\\usepackage{pslatex}\n"
                 #"\\usepackage{inconsolata}\n"
                 
                 ;; used for the table of the bugs
                 #"\\newcommand{\\ErrorDescriptionBox}[1]{"
                 #"\\begin{minipage}[t]{4in}#1\\end{minipage}}"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  An Empirical Comparison Between Random Generation and Enumeration
  for Testing Redex Models
}
@doi{}

@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]
@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]
@authorinfo["Jay McCarthy"
            "Brigham Young University"
            "jay@cs.byu.edu"]
@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]

@;{ Aaron's comments:

Hi, guys.

I read through your Putting Dependent Types to Work paper (actually more than once) a while back, but did not find a moment to write to you about it until just now, with baby napping...

I really like that you are tackling running time in type theory.  I think this is a major issue that has been largely ignored by the type theory community.  The monadic approach is a natural one, and since the type theory does not help you out (since it considers Ackermann(4,2) interchangeable -- syntactically indistinguishable -- from 2^65536 − 3), one has to resort to providing an interface where the semantics you are trying to enforce cannot actually be expressed inside the theory.  So this all seems really reasonable.  I also quite like the Braun tree example.  I did not know about this data structure, but can think of at least one interesting use for it.  And it is, of course, very nice that you can formally verify the results from Osaki about this data structure.

One piece of terminology I like with dependent types, which your paper made me think of, is internal versus external verification.  An internally verified artifact is one which, thanks to rich typing (or you could just say, imposition of invariants directly in the artifact), carries with it its own verification in some sense.  An externally verified artifact is one which has some property proved about it by a distinct proof artifact.  We can have internally and externally verified data structures: lists with length are internally verified, and lists where we impose some additional property outside the list itself (like, length l = 10, or sorted l, or something like that) are externally verified.  Functions can be internally verified, if they have pre- and post-conditions expressed in their types; or externally verified, if you write some theorem about them.  It is hard to see how to verify certain kinds of properties internally; algebraic properties like commutativity of addition or associativity of list append seem hard to express with the types of those functions.  When doing internal verification of a function, one could capture a precondition on a data structure internally or externally: either the function takes in x with a rich type, or x with a simple type together with a proof p about x.

So in your case, I would say your monad is supporting internal verification of functions, where you oropose using externally verified data structures (your functions take in binary trees together with proofs that they are Braun) for better extraction.

One quibble: I do not understand your choice of title, since lots of previous research has indeed been putting dependent types to work already, so this does not seem unique to your work.

That aside, I like the paper and wish you the best for acceptance at OOPSLA!

Cheers,
Aaron
}

@abstract{ 
          
This paper presents a benchmark suite of buggy Redex models
designed to test bug-finding techniques. Our benchmark
contains large and small models, easy and hard to find bugs,
bugs that we invented based on our experience programming in
Redex and bugs in models written by others that happened
during development.
  
We evaluate three testing techniques: a generic, ad hoc
random generator tuned for Redex programs, random selection
from a uniform distribution of Redex programs, and an
in-order enumeration of Redex programs.
  
Our results contradict commonly-held, yet unsubstantiated
wisdom regarding the relative value of these three
approaches. Specifically, selecting uniformly at random is
not the best-performing choice, and enumeration and ad hoc random
selection are incomparable, with random being better with
more than 10 minutes but in-order enumeration being better
in interactive time-frames.

}

@include-section["intro.scrbl"]

@include-section{combinators.scrbl}

@include-section["redex-enumeration.scrbl"]

@include-section{methodology.scrbl}

@include-section{benchmark.scrbl}

@include-section{results.scrbl}

@include-section{related.scrbl}

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]

