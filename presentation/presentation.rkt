#lang slideshow

(require racket/draw 
         redex/private/enumerator
         slideshow/code
         "../enum-util.rkt"
         "../results/plot.rkt"
         )


(define (as-tt x)
  (tt (format "~a" x)))
(slide (t "Enumerating Countable Sets for Property-Based Testing"))

;; Motivation
(slide (t "First, a demo"))

;; What
(slide #:title "Enumeration"
       (t "An enumeration consists of")
       (item "A Cardinality (natural number or infinite)")
       (item "An encoding function to-nat  : a → Nat")
       (item "A decoding function from-nat : Nat → a"))

(slide #:title "Examples"
       (item "Natural numbers: infinite, identity, identity")
       (item "Booleans: 2, 0 ↔ true and 1 ↔ false")
       (item "Integers: infinite, ...")
       'next
       (para "Manually constructing such bijections is tricky, prefer combinators"))

(slide #:title "What combinators?"
       'alts
       (list
        (list
         (code (define-language rbtrees
                 (tree  ::= empty
                            (node color val tree tree))
                 (color ::= red black)
                 (val   ::= number)))
                 
         (para "Need support for finite sets, alternatives, tuples, recursion (fix points)"))
        (list
         (t "Redex also supports more exotic patterns, guiding combinator design")
         (scale (table 2
                       (map as-tt
                            (list '(number_1 number_1) "Variable Bindings"
                                  '(number_!_1 number_!_1) "Dependence, finite filtering"
                                  '(number ...) "Sequencing"
                                  '(number ..._1 string ..._1) "Sequences of same length"))
                       cc-superimpose
                       cc-superimpose
                       10
                       10)
                0.75))))

(slide #:title "Design Goals"
       (t "Combinators should be")
       (item "Efficient (produced enumerations should have linear complexity in the length of the bitstring of the input number)")
       (item "Fair (not favor one of the argument enumerations over others)"))

(define-syntax-rule (define-with-code name code-name expr)
  (begin
    (define name expr)
    (define code-name (code expr))))

(define-with-code a-d/e fin-code (fin/e 'a 'b 'c 'd))
(slide #:title "Finite Enumerations"
       (t "Set Interpretation: Finite Sets")
       (code (fin/e 'a 'b 'c 'd))
       (foldr vl-append
              (blank)
              (map as-tt (to-list a-d/e))))
;; TODO: better version of this...
(define (enum-col e #:to-str [to-str (λ (x) (format "~s" x))])
  (define n (min (size e) 20))
  (foldr vl-append 
         (blank)
         (for/list ([x (in-list (approximate e n))])
           (tt (to-str x)))))
(define-with-code int-or-str/e i-c/e-code
   (disj-sum/e (cons integer/e integer?) (cons string/e string?)))
(slide #:title "Sum"
       (item "Set interpretation: Disjoint union")
       (item "disj-sum/e : enum a, enum b → enum (a or b)")
       (code disj-sum/e nat/e string/e)
       'next
       (enum-col int-or-str/e))
(define neg/e 
  (map/e (λ (x) (sub1 (- x)))
         (λ (x) (- (add1 x)))
         nat/e))
(slide #:title "Sum Example"
       'alts
       (list 
        (list
         (htl-append 10
                     (enum-col nat/e)
                     (enum-col neg/e)))
        (list (enum-col (disj-sum/e (cons nat/e number?) (cons neg/e number?))))))

(slide #:title "from-nat"
       (t "Just check if it's even or odd (constant time)"))

(slide #:title "Sum of 3 Things?"
       (t "Mathematically, it doesn't matter, just iterate")
       'alts
       (list
        (list
         (htl-append 10
                     (enum-col nat/e)
                     (enum-col neg/e)
                     (enum-col string/e)))
        (list 
         (htl-append 10
                     (enum-col (disj-sum/e (cons nat/e number?) (cons neg/e number?)))
                     (enum-col string/e )))
        (list 
         (enum-col (disj-sum/e (cons (disj-sum/e (cons nat/e number?) (cons neg/e number?)) number? ) (cons string/e string?))))))

(slide #:title "Sum, redefined"
       (item "disj-sum/e : enum a_1, enum a_2, ... → enum (a_1 or a_2 or ...)"))

(slide #:title "Sum of many"
       (item "Just need to do a quotient with remainder, still efficient")
       'alts
       (list 
        (list
         (htl-append 10
                     (enum-col nat/e)
                     (enum-col neg/e)
                     (enum-col string/e)))
        (list
         (enum-col (disj-sum/e (cons nat/e number?)
                               (cons neg/e number?)
                               (cons string/e string?))))))

(slide #:title "Sums of Finite Enumerations"
       (t "Easily generalizes to arbitrary sums of finite, infinite enumerations")
       'alts
       (list
        (list 
         (htl-append 10
                     (enum-col nat/e)
                     (enum-col (fin/e 'true 'false))
                     (enum-col (fin/e 'a 'b 'c 'd))))
        (list
         (enum-col (disj-sum/e (cons nat/e number?)
                               (cons (fin/e 'true 'false) boolean?)
                               (cons (fin/e 'a 'b 'c 'd) symbol?))))))

(slide #:title "Product"
       (item "Set interpretation: Cartesian Product")
       (item "cons/e : enum a, enum b → enum (a, b)"))

(define-with-code n-o-b/e n-o-b-c
  (cons/e nat/e (fin/e 'true 'false)))
(slide #:title "Finite Product"
       (t "For at least one finite product we'll just loop through the smaller enumeration")
       n-o-b-c
       (enum-col n-o-b/e))

(slide #:title "Infinite Product"
       (t "What order do we want?")
       (gen-grid cons/e 10 0 500 12 #:arrows? #f))

(slide #:title "Cantor Pairing Function"
       ;; TODO: latexify equation
       (para "Normally defined Nat*Nat → Nat, which is our to-nat, but for enumeration, the from-nat function is more important")
       (item "to-nat(n,m) = 1/2(n+m)(n+m+1) + m")
       (item "For from-nat we need to solve z = (n+m)(n+m+1)/2 + m for z")
       (item "With some ingenuity it's not so hard."))

(slide #:title "Geometric Interpretation"
       'alts
       (append
        (for/list ([i (in-range 21)])
         (list
          (gen-grid cantor-cons/e 10 i 500 12 #:arrows? #t)))
        (list (list (gen-grid cantor-cons/e 10 54 500 12 #:arrows? #t))
              (list (gen-grid cantor-cons/e 10 55 500 12 #:arrows? #f)))))

(slide #:title "Cantor from-nat"
       (para "First find the \"triangle root\" of the number, then use the \"triangle root remainder\" to locate it on that triangle."))

(slide #:title "Nested Pairing"
       (item "Once again nesting is too unfair to be used in general")
       (item "Enumerating the first 100000 terms of (nat * nat) * nat, the first two average ~7.5 while the third slot averages ~150"))

(slide #:title "Generalized Cantor N-Tupling"
       (para "Known \"fair\" generalization to Skolem at latest."
             "But apparently combinatoricists only care about the to-nat function")
       (item "n-th degree Diophantine equation...") ;; TODO: copy the formula from Tarau's paper
       ;; TODO: clean this up!
       (item "Known search procedure (Tarau) that generalizes well with a lot of enumerations, but scales poorly with the input natural number for small tuples (1-10) the kinds of things used in Redex!"))

(slide #:title "Back to the drawing board..."
       (para "An enumeration defines an order on the set."
             "The Cantor bijection orders by the sum of the terms indices."
             "Maybe order some other way?")
       (gen-grid cantor-cons/e 10 54 500 12 #:arrows? #t)
       (para "Instead of searching by layers of an n-simplex (triangle, tetrahedron)"
             "search by layers of an n-cube."))

(slide #:title "Boxy Tupling"
       (para "Order by the max instead of the sum?")
       'alts
       (append
        (for/list ([i (in-range 25)])
          (list (gen-grid boxy-cons/e 10 i 500 12 #:arrows? #t)))
        (list (list (gen-grid boxy-cons/e 10 99 500 12 #:arrows? #t))
              (list (gen-grid boxy-cons/e 10 100 500 12 #:arrows? #f)))))

(slide #:title "Boxy N-Tupling"
       (t "TODO: picture of boxy enumeration")
       (para "decode just need n-th root!"))

(slide #:title "Mixed finite/infinite N-tupling"
       (para "To minimize the interplay between them, we collect all of the finite enumerations and infinite enumerations into separate bins then tuple them separately and then tuple the result"))

(slide #:title "Fair?"
       (t "More on this later..."))

(slide #:title "Recursion"
       (t "Set interpretation: ?")
       (t "fix/e : (enum a → enum a), optional cardinality → enum a")
       (code (fix/e (λ (l/e) (disj-sum/e (fin/e '())
                                         (cons/e nat/e l/e))))))

(slide #:title "Recursion Caveats"
       (t "Order matters, the following diverges:")
       (code (fix/e (λ (l/e)
                      (disj-sum/e (cons/e nat/e l/e)
                                  (fin/e '()))))))

(define-with-code ord/e ord-code
  (dep/e nat/e nat+/e))
(slide #:title "Dependence"
       (t "Set interpretation: union of an indexed family of sets")
       (t "dep/e : enum a, (a -> enum f(a)) -> enum (a, f(a))")
       ord-code
       (enum-col ord/e)
       (t "Slow on some inputs, avoid whenever possible!"))

(define-with-code not-2/e not-2-code
  (except/e nat/e 2))
(slide #:title "Filter"
       (t "Set interpretation: subset")
       (para "General filter is slow/hard"
             "But removing finitely many (known) elements is easy!")
       (t "except/e : enum a, a → enum a")
       (para "Just use the to-nat function to find when it occurs, then skip it when indexing")
       not-2-code
       (enum-col not-2/e))

;; How

(slide #:title "Applications"
       (item "Testing")
       (item "Games"))

;; TODO: get colors better
(slide #:title "Redex patterns"
       'alts
       (list
        (list (item "Extract all variables into an environment, then plug them in at the end")
              'alts
              (list
               (list (code (nat_1 nat_1 string_2 string_2)))
               (list (htl-append (tt "{_1 → nat, _2 → string}") 
                                 (tt "(_1 _1 _2 _2)"))
                     (enum-col #:to-str (λ (x) (format "~a" x))
                               (map/e (λ (xy)
                                        (format "{_1 → ~a, _2 → ~s}" (car xy) (cdr xy))  )
                                      identity
                                      (cons/e nat/e string/e))))))
        (list (item "Disequality Constraints")
              (item "Extract variables into environment, keeping track of how many")
              (code (nat_!_1 nat_!_1 nat_!_1))
              (htl-append (tt "{_!_1 → nat * nat * nat }")
                          (tt "(0_!_1 1_!_1 2_!_1"))
              (item "Combination of dependence and filtering")
              (enum-col #:to-str identity
                        (map/e (λ (xs)
                                 (apply format "{_!_1 → (~a, ~a, ~a)}" xs))
                               identity
                               (uniq-list/e nat/e 3))))
        (list (item "Sequences")
              (code (number ... string ...))
              (item "Easy, just define listof/e using fix/e"))
        (list (item "Sequences of the same length")
              (code (nat ..._1 real ..._2 string ..._1 bool ..._2))
              'alts
              (list (list (t "Easy way: pick lengths and then generate lists of that length")
                          (t "But can we avoid dependency?"))
                    (list (t "Reorder, ")
                          (code ((nat string) ..._1 (real bool) ..._2))
                          'next
                          (t "Drop indices")
                          (code ((nat string) ... (real bool) ...))
                          (t "Recover the order later"))))))

(slide #:title "Evaluation"
       (item "What's the best way to use enumerations for testing?")
       (item "How does the enumeration compare to (ad-hoc) random generators?"))

(slide #:title "Enumeration Generation"
       'alts
       (list
        (list
         (item "In-order enumeration")
         (item "Known technique: see SmallCheck")
         (item "Deterministic"))
        (list
         (item "Random natural number indexing into an enumeration")
         (item "How to select a natural number?")
         (item "Sample from a geometric distribution, then pick an index between 2^n, 2^(n+1)")
         (item "Sensitive to the probability of 0, branching factor of the grammar"))))

(slide #:title "Comparison"
       (item "3 techniques: Old Random Generator, Random natural indexing, In-order enumeration")
       (item "6 Redex models with 3-9 bugs each"))

(slide #:title "Raw Results"
       (scale (res-plot-24hour) 1.5)
       (comment "Random finds more bugs, but in-order finds them faster"))

(slide #:title "Bugs found over Time"
       (scale (line-plot-24hour) 1.5)
       ;; TODO: get this pict too
       )

(slide #:title "Evaluation Conclusion"
       (para "In-order enumeration best at interactive time-scales, random for long-running"))

(slide #:title "Fairness...")
;; Who
(slide #:title "Related Work"
       (item "Enumeration")
       (subitem "Paul Tarau. Bijective Term Encodings.") (comment "Doesn't handle dependency or finite terms")
       (subitem "Duregård et al. FEAT: Functional Enumeration of Algebraic Types") (comment "Doesn't handle dependency")
       (item "Automated Testing")
       (subitem "Runciman et al. SmallCheck and Lazy SmallCheck")
       (subitem ""))
(slide #:title "Thanks"
       (item "Robby Findler")
       (item "Paul Tarau")
       (item "Jay McCarthy"))
(slide)
