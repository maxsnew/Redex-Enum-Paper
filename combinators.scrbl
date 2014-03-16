#lang scribble/sigplan

@(require scribble/manual)

An enumeration of is a bijection between a subset of the natural numbers
and a countable set of terms. We represent this as a function that encodes
a term as a natural number, a function to decode a natural number into a term
and a (possibly infinite) size of the set.

@(racketblock
  (struct enum (size from to))
  (define/contract (decode e n)
    (-> enum? exact-nonnegative-integer? any/c)
    (if (and (< n (enum-size e))
             (>= n 0))
        ((enum-from e) n)
        (redex-error 'decode "Index into enumerator out of range")))
  (define/contract (encode e a)
    (-> enum? any/c exact-nonnegative-integer?)
    ((enum-to e) a)))

We can now manually construct an enumeration from a hand-written bijection, 
but then we must manually verify that our function is bijective. It is more
convenient and less error-prone to instead use a combinator library to construct
enumerations that are bijective by construction.

It is convenient to build off of a few primitive enumerations. The empty
enumeration @(racket empty/e) consisting of no elements, the identity
enumeration @(racket nats/e) of the natural numbers themselves and
a function @(racket from-list/e)
that constructs an enumeration from any finite list (assumed
to have no duplicates).

@(racketblock
  (define empty/e 
    (enum 0 
          (λ (x) (error 'absurd)) 
          (λ (x) (error 'absurd))))
  (define nats/e
    (enum +inf.0 identity identity))
  (define (from-list/e l)
    (define rev-map
      (for/hash ([i (in-naturals)]
                 [x (in-list l)])
        (values x i)))
    (enum (length l)
              (λ (n)
                (list-ref l n))
              (λ (x)
                (hash-ref rev-map x)))))

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

@; TODO: decide what to show here.
@; TODO: Figure out how to show values for (cons/e nats/e nats/e)
@; TODO: show the triangle numbers.
@; TODO: split this code between the two previous paragraphs?
