#lang scribble/lncs

@(require pict
          scribble/manual
          racket/draw
          redex/private/enumerator
          plot
          scriblib/figure
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title{Fair Union}

Next we turn to @racket[disj-sum/e], the operation corresponding to the
union of several enumerators.
Recall that the arguments for @racket[disj-sum/e] are not just enumerators, but pairs
consisting of an enumerator and a predicate to that returns true if a
value is in that enumerator, in line with the Racket convention of
using untagged union types. We will denote a call to
@racket[disj-sum/e] with @racket[k] arguments by
@racket[(disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?))]
where given that @racket[x] is in one of the @racket[e_i], @racket[(1? x)] is true if there is some index @racket[i] such that @racket[(decode e_1 i)] is @racket[x].

@(define symbol/e (except/e var/e '||))
@racket[disj-sum/e] is relatively easy to define fairly. Given two infinite argument enumerations, we can simply alternate between one and the other, so the first ten elements of @racket[(disj-sum/e (nat/e nat?) (symbol/e sym?))] are simply the first five elements of @racket[nat/e] and @racket[string/e] interleaved, where @racket[symbol/e] is some enumeration of all Racket symbols:
@enum-example[(disj-sum/e (cons nat/e number?)
                          (cons symbol/e symbol?)) 10]

Again, to achieve fairness we cannot simply use the binary version of
@racket[disj-sum/e] arbitrarily. For example, if we defined
@(define (union-three/e ep_1 ep_2 ep_3)
   (define e_2 (car ep_2))
   (define 2?  (cdr ep_2))
   (define e_3 (car ep_3))
   (define 3?  (cdr ep_3))
   (define (2-or-3? x) (or (2? x) (3? x)))
   (disj-sum/e ep_1 (cons (disj-sum/e ep_2 ep_3) 2-or-3?)))
@racketblock[(define (union-three/e ep_1 ep_2 ep_3)
               (define e_2 (car ep_2))
               (define 2?  (cdr ep_2))
               (define e_3 (car ep_3))
               (define 3?  (cdr ep_3))
               (define (2-or-3? x) (or (2? x) (3? x)))
               (disj-sum/e ep_1 (cons (disj-sum/e ep_2 ep_3) 2-or-3?)))]
then enumerating the first 10 elements of               
@racket[(union-three/e (cons nat/e nat?) (cons symbol/e sym?) (cons float/e float?))]
is unfairly weighted to the first argument:
@(centered (disj-sum-pict/bad))

A fair generalization is fairly obvious. First we decode each argument
with the value @racket[0], then each with @racket[1], and so on. So
when given a call
@racket[(decode (disj-sum/e (cons e_1 1?) ... (cons e_k k?)) i)]
we divide @racket[i] by @racket[k], giving us a quotient of @racket[q]
and remainder of @racket[r]. Then we call @racket[(decode e_r q)]. We
see that, like @racket[list/e], we have a notion of "layers", if we
think of the input enumerations as infinitely tall columns side by
side, each layer is a horizontal slice of the columns. So using the same enumerations as before, @racket[(disj-sum/e (cons nat/e exact-integer?) (cons symbol/e sym?) (cons float/e float?))] looks like this:
@(centered (disj-sum-pict/good))
              
Unlike @racket[list/e], @racket[disj-sum/e] enumerator also has an
intuitive notion of fairness for finite enumerations. For example this
enumeration:
@racketblock[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) sym?)
                         (cons nat/e number?)
                         (cons (fin/e "x" "y") string?))]
cycles through its two finite enumeration arguments until they
are exhausted before producing the rest of the natural
numbers:
@enum-example[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                          (cons nat/e number?)
                          (cons (fin/e "x" "y") string?))
              14]
In general, this means that @racket[disj-sum/e] must track the
ranges of natural numbers when each finite enumeration is exhausted
to compute which enumeration to use for a given index.

@;{TODO: theorem style}

Now we formalize @racket[disj-sum/e] for our definition of a
combinator. Unfortunately @racket[disj-sum/e]'s arguments do not fit our
definition of a combinator, because it takes predicates as well as
enumerators. We could adapt the combinator definition to consider only
the decoding part of an enumerator, but doing so would add complexity
without increasing understanding, so we ignore the predicates for the
purposes of the proof. The @texmath{args} function for
@racket[disj-sum/e] when called with @racket[k] arguments is defined
by @texmath{args(i) = ([],\ldots,[r],\ldots,[])} where
@texmath{i / k = q} remainder @texmath{r} and the @texmath{[r]} was in
the @texmath{q}th element of the resulting tuple. The @texmath{build}
function returns the element of the only non-empty list in its
arguments, @texmath{build([],\ldots,[x],\ldots,[]) = x}.

Theorem: @racket[disj-sum/e] is fair

Proof.

Let @texmath{k} be the number of input enumerations. The sequence
@texmath{M_i = k(i+1)} is an infinite increasing sequence for which
when calling @texmath{args(j)} with all @texmath{j = 0} to
@texmath{j = M_i - 1 = k(i+1) - 1}, and collecting results into lists
@texmath{(L_1,\ldots,L_k)} each list @texmath{L_l} is the same,
specifically @texmath{[0,\cdots, i]}. We proceed by induction on
@texmath{i}.  For @texmath{i=0}, @texmath{M_0=k} and for
@texmath{j=0\cdots(k-1)}, we have @texmath{args(j)} is exactly
@texmath{([],\ldots,[0],\ldots,[])} where the non-empty list is the @texmath{j}th slot in the tuple soevery @texmath{L_l = [0]}.

Then assuming this holds for @texmath{M_i}, for @texmath{M_{i+1} = k(i+2)}
by inductive hypothesis, if we call @texmath{args(j)} with @texmath{j}
from @texmath{0} to @texmath{M_i-1=k(i+1)-1} and concatenate column-wise into
lists @texmath{(A_1,\ldots,A_k)}, all of @texmath{A_1,\ldots,A_k}
are equivalent. Thus we need only show that calling @texmath{args(j)}
with @texmath{j} from @texmath{M_i = k(i+1)} to
@texmath{M_{i+1}-1=k(i+2)-1} and concatenating column-wise into lists
@texmath{(B_1,\ldots,B_k)} means that all of @texmath{B_1,\ldots,B_k}
are equivalent. Similarly to the base case, @texmath{args(k(i+2) + j)}
is equal to @texmath{([],\ldots,[k(i+1)],\ldots,[])} where the
@texmath{k(i+1)} is in the @texmath{j}th slot, so
@texmath{B_l = [k(i+1)]} for each @texmath{l=1,\ldots,k}. Thus
@racket[disj-sum/e] is fair.

Next we turn to @racket[union-three/e]. Its build function is the same as the build function for @racket[disj-sum/e] specialized to three arguments. Its args function is defined by

@raw-latex{\[args(i) = \begin{cases} ([\lfloor i/2 \rfloor],[],[]) & \text{if } i=2 \text{ mod } 2\\ ([],[\lfloor i/4 \rfloor],[]) & \text{if } i=1 \text{ mod } 4 \\ ([],[],[\lfloor i/4 \rfloor]) & \text{if } i=3 \text{ mod } 4 \end{cases} \]}

Theorem: @racket[union-three/e] is unfair.

Proof.

Now we will show that, similarly to the proof that @racket[triple/e]
is unfair, for any @texmath{n > 4} there is an @texmath{i < n} and
@texmath{h} such that @texmath{args(i) = ([h],[],[])} but there is no
@texmath{j < n} such that @texmath{args(i) = ([],[h],[])}. In that
case, the lists @texmath{L_1,L_2} produced by concatenating
column-wise in calls of @texmath{args(i)} for @texmath{i=0,\ldots,n-1}
would not be equivalent.

This relies on two elementary properties of the @texmath{args}
function. First, there is some @texmath{j\in 0,\ldots,n-1} such that
@texmath{args(j) = ([\lfloor (n-1)/2 \rfloor],[],[])}. This is true
because either @texmath{n-1} is even, so
@texmath{args(n-1) = ([\lfloor (n-1)/2 \rfloor],[],[])} or
@texmath{n-1} is odd, so
@texmath{\lfloor (n-1)/2 \rfloor = \lfloor (n-2)/2 \rfloor} and
@texmath{args(n-2) = ([\lfloor (n-2)/2 \rfloor],[],[])}.
Second, for every @texmath{j\in 0,\ldots,n-1} such that
@texmath{args(j) = ([],h,[])} for some @texmath{h},
@texmath{h \le \lfloor (n-1)/4\rfloor} which is a direct consequence
of the definition of @texmath{args}.
Finally, we rely on that fact that for @texmath{n > 9},
@texmath{\lfloor (n-2)/2\rfloor > \lfloor (n-1)/4\rfloor}, or
equivalently that for @texmath{n > 8},
@texmath{\lfloor(n-1)/2\rfloor > \lfloor n/4\rfloor > 0}.

Thus for any @texmath{n} there is a value in @texmath{L_1} that is
greater than any in @texmath{L_2}, so @texmath{L_1} and @texmath{L_2}
are not equivalent, so @racket[decode-three] is unfair.
