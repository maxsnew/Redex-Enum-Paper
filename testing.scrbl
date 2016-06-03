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
          (prefix-in 2: 2htdp/image))

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
that checks to see if a binary tree is a binary search tree:
@racketblock/define[(struct node (n l r))
                    (define (bst? t)
                      (match t
                        [#f #f]
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

We can easily code this up, too:
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

To use property-based testing to uncover the difference between these two functions,
we need a source of binary trees and then we can simply compare the results
of the two functions. This is where enumerations come in. They allow to describe a mapping
between the natural numbers and arbitrary data-structures. Then we can simply choose
some natural numbers, map them to binary trees and see if we can find a difference
between the two predicates.


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

@(define bt/e
   (or/e (fin/e #f)
         (list/e natural/e
                 (delay/e bt/e)
                 (delay/e bt/e))))

@(define un-bt/e
   (or/e (fin/e #f)
         (unfair-cons/e
          natural/e
          (unfair-cons/e
           (delay/e un-bt/e)
           (delay/e un-bt/e)))))

@(define (to-pair-bst t)
   (match t
     [#f #f]
     [(node n t1 t2) (cons n (cons (to-pair-bst t1) (to-pair-bst t2)))]))

@(define (to-list-bst t)
   (match t
     [#f #f]
     [(node n t1 t2) (list n (to-list-bst t1) (to-list-bst t2))]))

@(define t (node 0
                 (node 0 #f (node 1 #f #f))
                 #f))

@(begin
   ;; check that the example really is what we want it to be
   (when (bst? t) (error 'testing.scrbl "t is not a bst"))
   (unless (not-quite-bst? t) (error 'testing.scrbl "t is a wrong-bst")))

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

If we use fair combinators, we find that the smallest natural that demonstrates the
difference is @(add-commas (to-nat bt/e (to-list-bst t))). If we unfair combinators,
then that same tree appears only at position
@;; trick to get latex to break the line in a reasonable way
@(element (style "relax" '(exact-chars))
          (regexp-replace*
           #rx","
           (add-commas (to-nat un-bt/e (to-pair-bst t)))
           ",\\\\hskip 0pt{}"))
and, as far as we know, there are no counterexamples that appear at smaller indicies.
This is the tree in question:

@centered{@render-t[t]}