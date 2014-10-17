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
@;{TODO: write this section..}

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

Theorem: @racket[disj-sum/e] is fair

Proof.

We claim that @racket[disj-sum/e] is fair. When called with
@texmath{k} arguments @racket[e_1 e_2 ... e_k] the sequence
@texmath{M_i = k(i+1)} is an infinite increasing sequence for which
when enumerating
@racket[(disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?))]
with all indices greater than or equal to
@texmath{0} and less than @texmath{M_i=k(i+1)} the enumerations
@racket[e_1 e_2 ... e_k] are called with the same arguments,
specifically @texmath{0\cdots i}. We proceed by induction on
@texmath{i}.  For @texmath{i=0}, @texmath{M_0=k} and for
@texmath{j=0\cdots(k-1)}, we have
@racket[(decode (disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?)) j)]
is exactly
@racket[(decode e_{j+1} 0)] so each argument is called with the same
number @texmath{0} exactly once. Then assuming this holds for
@texmath{M_i}, for @texmath{M_{i+1} = k(i+2)} we know by inductive
hypothesis that decoding from @texmath{0} to @texmath{M_i=k(i+1)}
calls all arguments with the same values so we need only show that
decoding from @texmath{M_i=k(i+1)} up to but not including
@texmath{M_{i+1}=k(i+2)} uses all arguments equally, and similarly to
the base case, by the definition of @racket[disj-sum/e],
@racket[(decode (disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?)) (+ (* k (+ i 1)) j))]
is equal to @racket[(decode e_{j+1} (* k (+ i 1)))] so all arguments
are called with the same value. Thus @racket[disj-sum/e] is fair.

@;{TODO: (disj-sum/e (e_1 1?) ((disj-sum/e (e_2 2?) (e_3 3?)) (or 2? 3?)))}
Theorem: @racket[union-three/e] is unfair.

Proof.
First, we define @racket[union/e] to be the resulting enumeration from
a call to
@racket[(union-three/e (cons e_1 1?) (cons e_2 2?) (cons e_3 3?))].
We use the following equivalent definition for the decoding function
of @racket[union/e]:

@racketblock[(define (decode-three i)
               (define (q r) (quotient/remainder i 3))
               (match r
                 [1 (decode e_2 (quotient q 2))]
                 [3 (decode e_3 (quotient q 2))]
                 [else (decode e_1 q)]))]
                 
Now we will show that, similarly to the proof that @racket[triple/e]
is unfair, for any @texmath{n > 4} there is an @texmath{i < n} and
@texmath{h} such that @racket[(decode union/e i)] is equal to
@racket[(decode e_1 h)] but there is no @texmath{j} such that
@racket[(decode union/e j)] is @racket[(decode e_2 h)]. In other
words, for any @texmath{n > 4}, when enumerating all values of
@racket[union/e] from @racket[0] to @racket[n], @racket[e_1] has been
called with an index with which @racket[e_2] has not been called.

This relies on two basic properties of @racket[decode-three]. First,
that when enumerating all indices @racket[0] to @racket[n],
@racket[e_1] has been called with the index @texmath{\lfloor n/2\rfloor}.
Second, that when enumerating all indices @racket[0] to @racket[n],
@racket[e_2] has been called with indices that are all less than or
equal to @texmath{\lfloor(\lfloor n/2\rfloor)/2\rfloor}.  Both of
these properties are direct from the definition of
@racket[decode-three]. Then, we note that for @texmath{n>4},
@texmath{n - (\lfloor n/2\rfloor) > 2} so for @texmath{n>4},
@texmath{\lfloor(\lfloor n/2\rfloor)/2\rfloor < \lfloor n/2\rfloor} so
the largest value indexed into @racket[e_1] has not been used to index
into @racket[e_2]. Thus @racket[decode-three] is unfair.
