#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          "util.rkt")

An enumeration of is a bijection between a subset of the natural numbers
and a countable set of terms. We represent this as a function that encodes
a term as a natural number, a function to decode a natural number into a term
and a (possibly infinite) size of the set.

We can now manually construct an enumeration from a hand-written bijection, 
but then we must manually verify that our function is bijective. It is more
convenient and less error-prone to instead use a combinator library to construct
enumerations that are bijective by construction.

It is convenient to build off of a few primitive enumerations. The empty
enumeration @(racket empty/e) consisting of no elements, the identity
enumeration @(racket nats/e) of the natural numbers themselves and
a function @(racket from-list/e)
that constructs an enumeration from any finite list (assumed
to have no duplicates). We will show examples using the @(racket approximate)
function that returns a prefix of an enumeration as a list.
@(interact (decode empty/e 0))
@(interact (approximate nats/e 10))
@(interact (decode (from-list/e '(a b c)) 1))
@(interact (encode (from-list/e '(a b c)) 'b))

One fundamental combinator is the pairing operator @(racket cons/e), that takes 2 enumerations
and returns an enumeration of pairs of those values. If one of the enumerations
is finite, the bijection loops through the finite enumeration, pairing each with
an element from the other enumeration. If both are finite, we loop through the
one with lesser cardinality. This corresponds to taking the quotient with
remainder of the index with the lesser size.

However an infinite enumeration requires more care. If we imagine our sets
as being laid out in an infinite table, this operator zig-zags through the
table to enumerate all pairs, so that the sum of the encoded values in each
side of the pair increases with the index. To find the proper depth, we must
find the smallest so-called "triangle number", the partial sums of the infinite
sum of natural numbers.

@(interact (approximate (cons/e nats/e nats/e) 10))
@; TODO: show the triangle numbers?

@; TODO: show examples?
Another fundamental combinator is the disjoint union operator @(racket disj-sum/e)
that takes two or more enumerators and predicates to distinguish between their elements and 
returns an enumeration of their union. The resulting enumeration alternates between the 
input enumerations, so that if every input enumeration is infinite, then each
element is
@;; Simplified to only show infinite case
@;; TODO: fix so the code isn't going off the edge of the page
@(racketblock
  (define (disj-sum/e . e-ps)
    (cond [(empty? e-ps) empty/e]
          [(not (andmap (compose infinite? size) e-ps)) ...] ;; Finite case
          [else ;; all infinite
           (define es (map car e-ps))
           (define ps (map cdr e-ps))
           (define (dec n)
             (define-values (q r) (quotient/remainder n (length es)))
             (decode (list-ref es r) q))
           (define (enc x)
             (define (find-e n p? p?s)
               (cond [(or (empty? p?s) (p? x)) n]
                     [else (find-e (add1 n) (car p?s) (cdr p?s))]))
             (define n (find-e 0 (car ps) (cdr ps)))
             (define e (list-ref es n))
             (+ n (* (encode e x) (length es))))
           (enum +inf.0 dec enc)])))
@;TODO: talk about finite case?

@; TODO: fix/e and thunk/e
Recursive enumerations can be easily constructed with a fix-point combinator,
though in general a more open method is prefered. We implement mutual recursion
using references and a primitive combinator that delays evaluation.
But how do we determine the size of a recursive enumeration? Our combinators rely
on statically knowing the sizes of their arguments, but in a recursive enumeration
this is begging the question! Since it is not possible to statically know
whether a recursive enumeration uses its parameter, we leave it to the caller
to determine the correct size.
@(racketblock
  (define (thunk/e s thunk)
    (define promise/e (delay (thunk)))
    (enum s
          (λ (n)
            (decode (force promise/e) n))
          (λ (x)
            (encode (force promise/e) x))))
  (define (fix/e s f)
    (thunk/e s 
             (λ () (f (fix/e s f))))))

With pairing, alternation and recursion, we have the building blocks of algebraic
data types. It is now straightforward to define an enumeration of lists of a 
given type.
@(racketblock
  (define (many/e e)
    (define s 
      (if (= 0 (size e))
          1
          +inf.0))
    (fix/e s
           (λ (self)
             (disj-sum/e (cons (const/e '())   null?)
                         (cons (cons/e e self) pair?))))))

@; TODO: except/e
An advantage of encoding both sides of the bijection that defines an enumeration
is the ability to filter individual elements. 
@(racketblock
  (define (except/e e x)
    (define excepted (encode e x))
    (define (dec n)
      (decode e
              (if (n . < . excepted)
                  n
                  (sub1 n))))
    (define (enc y)
      (define n (encode e y))
      (if (n . < . excepted)
          n
          (add1 n)))))
Allowing us to easily write a function that enumerates non-empty lists.
@(racketblock
  (define (many1/e e)
    (except/e e '())))

@; TODO: examples of other derived combinators?