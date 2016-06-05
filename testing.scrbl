#lang scribble/base

@(require scribble/manual
          scribble/eval
          scriblib/figure
          racket/list
          racket/contract
          racket/format
          racket/match
          data/enumerate/lib
          data/enumerate/private/unfair
          scriblib/footnote
          scribble/core
          "util.rkt"
          "enum-util.rkt"
          "cite.rkt"
          pict/tree-layout
          (prefix-in p: pict)
          (prefix-in 2: 2htdp/image)
          rackunit)


@(provide bt/e un-bt/e (struct-out node)
          bst? not-quite-bst?
          smallest-known-un-bt/e-example-t
          render-t)

@title[#:tag "sec:intro-testing"]{Enumeration in Property-based Testing}

Our interest in enumeration is motivated by property-based
testing, as popularized by Quickcheck@~cite[quickcheck].
Property-based testing enables programmers to simply and
effectively test their software by supplying a property
that a program should have and then generating a large
supply of examples and testing to see if any of them falsify
that property.

To see how bijective enumerations can help with property-based
testing, consider this snippet of Racket@~cite[plt-tr1] code
that checks to see if a given binary tree is a binary search tree:
@racketblock/define[(struct node (n l r) #:transparent)

                    (define (bst? t)
                      (match t
                        [#f #t]
                        [(node n l r)
                         (and (check-all l (λ (i) (<= i n)))
                              (check-all r (λ (i) (>= i n)))
                              (bst? l)
                              (bst? r))]))
                    
                    (define (check-all t p?)
                      (match t
                        [#f #t]
                        [(node n l r)
                         (and (p? n)
                              (check-all l p?)
                              (check-all r p?))]))]
The first line defines a node struct with three fields (@racket[n] for
the value in the node, @racket[l] for the left subtree, and @racket[r]
for the right subtree). The @racket[bst?] function recursively
checks the tree, ensuring that the value in each node is larger
than all of the values in the left subtree and smaller than all of the
values in the right subtree.

While this function is correct, the algorithm it uses is inefficient, because
to repeatedly processes subtrees as it recurs over the structure of the tree,
running in @texmath{O(n^2)}.
A better algorithm would make only a single pass over the tree. The basis for a
naive and incorrect function that makes such a single pass is the false observation
that, for each node, if the root of the left subtree is smaller than the
value in the node and the root of the right subtree is larger, then the tree is
a binary search tree.

We can easily write this (incorrect) code, too:
@racketblock/define[(define (not-quite-bst? t)
                      (match t
                        [#f #t]
                        [(node n l r)
                         (and (<= (or (root-n l) -inf.0)
                                  n
                                  (or (root-n r) +inf.0))
                              (not-quite-bst? l)
                              (not-quite-bst? r))]))
                    
                    (define (root-n t)
                      (match t
                        [#f #f]
                        [(node n l r) n]))]

To use property-based testing to uncover the difference
between these two functions, we need a source of binary
trees and then we can simply compare the results of the two
functions. This is where enumerations come in. They allow us
to describe a mapping between the natural numbers and
arbitrary data-structures. Then we can simply choose some
natural numbers, map them to binary trees and see if we can
find a difference between the two predicates.

@(define (unfair-cons/e e1 e2)
   (map/e #:contract (λ (x)
                       ((cons/c (enum-contract e1)
                                (enum-contract e2)) x))
          (λ (n)
            (define-values (x y) (unfair-n->n*n n))
            (cons (from-nat e1 x)
                  (from-nat e2 y)))
          (λ (pr)
            (unfair-n*n->n (to-nat e1 (car pr))
                           (to-nat e2 (cdr pr))))
          natural/e))

@(define bt?
   (λ (l)
     (match l
       [#f #t]
       [(node n l r) (and (exact-nonnegative-integer? n)
                          (bt? l)
                          (bt? r))]
       [_ #f])))

@(define bt/e
   (map/e
    (λ (l-t)
      (let loop ([l-t l-t])
        (match l-t
          [#f #f]
          [(list n l r) (node n (loop l) (loop r))])))
    (λ (n-t)
      (let loop ([n-t n-t])
        (match n-t
          [#f #f]
          [(node n l r) (list n (loop l) (loop r))])))
    (letrec ([bt/e
              (or/e (fin/e #f)
                    (list/e natural/e
                            (delay/e bt/e)
                            (delay/e bt/e)))])
      bt/e)
    #:contract bt?))

@(define un-bt/e
   (or/e (fin/e #f)
         (map/e
          (λ (l) (match l [(cons n (cons l r)) (node n l r)]))
          (λ (n) (match n [(node n l r) (cons n (cons l r))]))
          (unfair-cons/e
           natural/e
           (unfair-cons/e
            (delay/e un-bt/e)
            (delay/e un-bt/e)))
          #:contract node?)))

@(define smallest-known-un-bt/e-example-t
   (node 0
         (node 0 #f (node 1 #f #f))
         #f))

@(define smallest-bt/e-example-t
   (let/ec k
     (let/ec k
       (for ([i (in-naturals)])
         (define t (from-nat bt/e i))
         (when (and (not (bst? t)) (not-quite-bst? t))
           (k t))))))

@(begin
   ;; check that the example really is what we want it to be
   (when (bst? smallest-known-un-bt/e-example-t)
     (error 'testing.scrbl "t is not a bst"))
   (unless (not-quite-bst? smallest-known-un-bt/e-example-t)
     (error 'testing.scrbl "t is a wrong-bst")))

@(begin
   (check-true (bst? #f))
   (check-true (bst? (node 0 #f #f)))
   (check-true (bst? (node 1 (node 0 #f #f) (node 2 #f #f))))
   (check-false (bst? (node 1 (node 2 #f #f) (node 2 #f #f))))
   (check-false (bst? (node 1 (node 0 #f #f) (node 0 #f #f)))))

@(define (render-t t)
   (define biggest -inf.0)
   (check-all t (λ (i) (set! biggest (max i biggest))))
   (define bkg (let* ([space (p:ghost (p:text (~a biggest)))]
                      [size (max (p:pict-width space) (p:pict-height space))])
                 (p:cc-superimpose
                  (2:circle size 'solid "white")
                  (2:circle size
                            'outline
                            (2:pen "gray" 4 "solid" "round" "round")))))
   (binary-tidier
    (let loop ([t t])
      (match t
        [#f #f]
        [(node n l r) (tree-layout
                       #:pict (p:cc-superimpose bkg (p:text (~a n)))
                       (loop l) (loop r))]))))

One effective approach to generating natural numbers is to simply count, starting
at 0. If we use fair combinators, we find that the smallest natural that demonstrates the
difference is @(add-commas (to-nat bt/e smallest-bt/e-example-t)). If we
swap out the fair pairing combinator for an unfair one based on the bijection discussed
in the introductino, then that same tree appears at a position with
@(add-commas (string-length (~a (to-nat un-bt/e smallest-bt/e-example-t))))
digits. The smallest index that we know has a counter exmaple is this
@(add-commas (string-length (~a (to-nat un-bt/e smallest-known-un-bt/e-example-t))))
digit number:
@;; trick to get latex to break the line in a reasonable way
@(element (style "relax" '(exact-chars))
          (regexp-replace*
           #rx","
           (add-commas (to-nat un-bt/e smallest-known-un-bt/e-example-t))
           ",\\\\hskip 0pt{}")).
That might not be the first counterexample,
but we do know that there are no counterexamples in the first 100 million naturals.
These are the two trees; the one on the left is the counterexample
at position @(add-commas (to-nat bt/e smallest-bt/e-example-t)) in the
fair enumerator and the one of the right is the smallest known counterexample
when using the unfair combinators.
@centered{@(p:ht-append 60
                        (render-t smallest-bt/e-example-t)
                        (render-t smallest-known-un-bt/e-example-t))}

