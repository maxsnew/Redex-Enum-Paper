#lang racket
(require redex
         pict
         (prefix-in : data/enumerate/lib))

(provide semantics-figure
         sr L to-enum
         e? T? v?
         (contract-out
          [from-nat+trace
           (-> e? exact-nonnegative-integer? 
               (values any/c
                       (hash/c exact-nonnegative-integer?
                               (set/c exact-nonnegative-integer?))))]))

(define-language L
  (e ::= 
     natural/e
     (or/e e e)
     (cons/e e e)
     (map/e f f e)
     (dep/e e f)
     (except/e e v)
     (fix/e x e)
     (trace/e n e)
     x)
  (v ::= (cons v v) n)
  (n ::= integer)
  (x ::= variable-not-otherwise-mentioned)
  
  (ae ::=
      (+ ae ae) (/ ae ae) (* ae ae)
      (- ae ae) (- ae ae ae)
      (integer-sqrt ae) (sqr ae)
      (< ae ae) (>= ae ae)
      n)
  
  (T ::= ∅ (n ↦ (n n ...) T))
  
  (f ::= 
     swap-cons
     (swap-zero-with natural)
     nat->map-of-swap-zero-with))
(define e? (redex-match L e))
(define T? (redex-match L T))
(define v? (redex-match L v))

(define-judgment-form L
  #:mode (@ I I O O)
  #:contract (@ e natural v T)
  
  [-------------------- "natural"
   (@ natural/e n n ∅)]
  
  [(even n) (@ e_1 (ae-interp (/ n 2)) v T)
   ---------------------------------------------  "or l"
   (@ (or/e e_1 e_2) n (cons 0 v) T)]
  
  [(odd n) (@ e_2 (ae-interp (/ (- n 1) 2)) v T)
   -------------------------------------------------- "or r"
   (@ (or/e e_1 e_2) n (cons 1 v) T)]
  
  [(side-condition (ae-interp
                    (< (- n (sqr (integer-sqrt n)))
                       (integer-sqrt n)))) (@ e_1 (ae-interp (- n (sqr (integer-sqrt n)))) v_1 T_1)
   (@ e_2 (ae-interp (integer-sqrt n)) v_2 T_2)
   ----------------------------------------------------------- "cons x"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))]
  
  [(side-condition (ae-interp
                    (>= (- n (sqr (integer-sqrt n)))
                        (integer-sqrt n)))) (@ e_1 (ae-interp (integer-sqrt n)) v_1 T_1)
   (@ e_2 (ae-interp (- n (sqr (integer-sqrt n)) (integer-sqrt n))) v_2 T_2)
   ---------------------------------------------------------------------------------------- "cons y"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))] 
  
  [(@ e n v_1 T)
   (where v_2 (Eval-bij (f_1 v_1))) (where v_1 (Eval-bij (f_2 v_2)))
   -----------------------------------------------------------------  "map"
   (@ (map/e f_1 f_2 e) n v_2 T)]
  
  [(@ (cons/e e natural/e) n_1 (cons v_1 n_2) T_1)
   (@ (Eval-enum (f v_1)) n_2 v_2 T_2)
   ----------------------------------------------  "dep"
   (@ (dep/e e f) n_1 (cons v_1 v_2) (⊕ T_1 T_2))]

  [(@ e (ae-interp n_2) v_2 T) (side-condition (ae-interp (< n_2 n_1)))
   ---------------------------------------- "ex<"
   (@ (except/e e n_1) n_2 v_2 T)]

  [(@ e_1 (ae-interp (+ n_2 1)) v_2 T) (side-condition (ae-interp (>= n_2 n_1)))
   ---------------------------------------- "ex>"
   (@ (except/e e_1 n_1) n_2 v_2 T)]

  [(@ (subst e x (fix/e x e)) n v T)
   --------------------------------- "fix"
   (@ (fix/e x e) n v T)]
  
  [(@ e n_2 v T)
   ----------------------------------------------  "trace"
   (@ (trace/e n_1 e) n_2 v (singleton n_1 n_2))])

;; assumes closed "e"s
(define-metafunction L
  subst : e x e -> e
  [(subst e_2 x e_1)
   ,(let loop ([e (term e_2)])
      (match e
        [`(fix/e ,x2 ,e)
         (if (equal? x2 (term x))
             `(fix/e ,x2 ,e)
             `(fix/e ,x2 ,(loop e)))]
        [(? list?) (map loop e)]
        [(? symbol?) (if (equal? e (term x)) (term e_1) e)]))])
 
(define-metafunction L
  ⊕ : T T -> T
  [(⊕ ∅ T) T]
  [(⊕ (n_1 ↦ (n_2 ...) T_1) T_2) (⊕ T_1 (join n_1 (n_2 ...) T_2))])

(define-metafunction L
  join : n (n ...) T -> T
  [(join n_1 (n_2 ...) ∅) (n_1 ↦ (n_2 ...) ∅)]
  [(join n_1 (n_2 ...) (n_1 ↦ (n_3 ...) T))
   (n_1 ↦ ,(sort (remove-duplicates (term (n_2 ... n_3 ...))) <) T)]
  [(join n_1 (n_2 ...) (n_3 ↦ (n_4 ...) T))
   (n_3 ↦ (n_4 ...) (join n_1 (n_2 ...) T))])

(define-metafunction L
  singleton : n n -> T
  [(singleton n_1 n_2) (n_1 ↦ (n_2) ∅)])

(define-metafunction L
  Eval-bij : (f any) -> any
  [(Eval-bij (swap-cons (cons v_1 v_2))) (cons v_2 v_1)]
  [(Eval-bij ((swap-zero-with n) 0)) n]
  [(Eval-bij ((swap-zero-with n) n)) 0]
  [(Eval-bij (f any)) any])

(define-metafunction L
  Eval-enum : (f any) -> any
  [(Eval-enum (nat->map-of-swap-zero-with natural))
   (map/e (swap-zero-with natural) (swap-zero-with natural) natural/e)]
  [(Eval-enum (f any)) natural/e])

(define-judgment-form L
  #:mode (odd I)
  #:contract (odd n)
  [(side-condition ,(odd? (term n)))
   ---------
   (odd n)])

(define-judgment-form L
  #:mode (even I)
  #:contract (even n)
  [(side-condition ,(even? (term n)))
   ---------
   (even n)])

(define-metafunction L
  ae-interp : ae -> natural or boolean
  [(ae-interp (+ ae_1 ae_2)) ,(+ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (- ae_1 ae_2)) ,(- (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (- ae_1 ae_2 ae_3)) (ae-interp (- ae_1 (+ ae_2 ae_3)))]
  [(ae-interp (/ ae_1 ae_2)) ,(/ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (* ae_1 ae_2)) ,(* (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (< ae_1 ae_2)) ,(< (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (>= ae_1 ae_2)) ,(>= (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (integer-sqrt ae)) ,(integer-sqrt (term (ae-interp ae)))]
  [(ae-interp (sqr ae)) ,(sqr (term (ae-interp ae)))]
  [(ae-interp n) n])

(define-metafunction L
  to-enum : e -> any
  [(to-enum (or/e e_1 e_2))
   ,(let ([e1 (term (to-enum e_1))]
          [e2 (term (to-enum e_2))])
      (:or/e (:map/e (λ (x) (cons 0 x))
                     cdr
                     e1
                     #:contract (cons/c 0 (:enum-contract e1)))
             (:map/e (λ (x) (cons 1 x))
                     cdr
                     e2
                     #:contract (cons/c 1 (:enum-contract e2)))))]
  [(to-enum (cons/e e_1 e_2))
   ,(:cons/e (term (to-enum e_1))
             (term (to-enum e_2)))]
  [(to-enum natural/e) ,:natural/e]
  [(to-enum (map/e (swap-zero-with natural) (swap-zero-with natural) e))
   ,(let ([e (term (to-enum e))]
          [swapper
           (λ (x) (if (exact-nonnegative-integer? x)
                      (cond
                        [(= x (term natural)) 0]
                        [(= x 0) (term natural)]
                        [else x])
                      x))])
      (:map/e swapper swapper e #:contract (:enum-contract e)))]
  [(to-enum (map/e swap-cons swap-cons e)) 
   ,(let ([e (term (to-enum e))]
          [swap (λ (x) (if (pair? x) (cons (cdr x) (car x)) x))])
      (:map/e swap swap e #:contract (:enum-contract e)))]
  [(to-enum (map/e any any e)) (to-enum e)]
  [(to-enum (dep/e e nat->map-of-swap-zero-with))
   ,(:dep/e (term (to-enum e))
            (λ (x)
              (if (exact-nonnegative-integer? x)
                  (term (to-enum (map/e (swap-zero-with ,x) (swap-zero-with ,x) natural/e)))
                  :natural/e)))]
  [(to-enum (dep/e e any)) (to-enum (cons/e e natural/e))]
  [(to-enum (except/e e n))
   ,(let ([e (term (to-enum e))])
      (:except/e e (:from-nat e (term n))))]
  [(to-enum (fix/e x e))
   ,(letrec ([d (:delay/e converted-e)]
             [converted-e
              (parameterize ([env (hash-set (env) (term x) d)])
                (term (to-enum e)))])
      converted-e)]
  [(to-enum x)
   ,(hash-ref (env) (term x))]
  [(to-enum (trace/e n e)) (to-enum e)])

(define env (make-parameter (hash)))

(define-metafunction L
  to-val : v -> any
  [(to-val n) n]
  [(to-val (cons v_1 v_2)) ,(cons (term (to-val v_1)) (term (to-val v_2)))])

(define (to-trace orig-T)
  (let loop ([T orig-T])
    (match T
      [`∅ (hash)]
      [`(,n1 ↦ (,n2 ...) ,T)
       (define ht (loop T))
       (when (hash-ref ht n1 #f)
         (error 'get-trace "got multiple mappings of ~a for ~s" n1 orig-T))
       (unless (equal? (remove-duplicates n2) n2)
         (error 'get-trace "not a set @ ~a for ~s" n1 orig-T))
       (hash-set ht n1 (apply set n2))])))

(define (try-one e n)
  (define enum (term (to-enum ,e)))
  (define ans (judgment-holds (@ ,e ,n v T) (to-val v)))
  (and (pair? ans) 
       (null? (cdr ans))
       (equal? (car ans) (:from-nat enum n))))

(define (from-nat+trace e i)
  (define trs (judgment-holds (@ ,e ,i v T) (v T)))
  (unless (and (pair? trs) (= 1 (length trs)))
    (error 'get-trace "got bad judgment-form result ~s" trs))
  (define ht (make-hash))
  (define T (cadr (car trs)))
  (define v (car (car trs)))
  (values (term (to-val ,v)) (to-trace T)))

(define (get-trace e i)
  (define-values (val trace) (from-nat+trace e i))
  trace)

(define (w/rewriters/proc thunk)
  
  (define (to-sexp lws)
    (let loop ([lws lws])
      (cond
        [(string? lws) (read (open-input-string lws))]
        [(symbol? lws) lws]
        [(boolean? lws) lws]
        [(number? lws) lws]
        [(list? lws)
         (for/list ([lw (in-list (cdr (reverse (cdr (reverse lws)))))])
           (loop (lw-e lw)))]
        [else (error 'to-sexp "unk ~s\n" lws)])))
  
  (define (ae->pict ae)
    (let loop ([needs-parens? #f]
               [ae ae])
      (match ae
        [`(+ ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (t " + ")
                      (loop #t ae2)))]
        [`(- ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (t " - ")
                      (loop #t ae2)))]
        [`(- ,ae1 ,ae2 ,ae3)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (t " - ")
                      (loop #t ae2)
                      (t " - ")
                      (loop #t ae3)))]
        [`(* ,(? simple? ae1) ,(? simple? ae2))
         (htl-append (loop #t ae1)
                     (loop #t ae2))]
        [`(< ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #f ae1)
                      (t " < ")
                      (loop #f ae2)))]
        [`(>= ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #f ae1)
                      (t " ≥ ")
                      (loop #f ae2)))]
        [`(integer-sqrt ,(? symbol? n))
         (define var (it (format "~a" n)))
         (define line (inset (hline (pict-width var)) 0 1 0 0))
         (define left-side (t "√"))
         (hbl-append (t "⌊")
                     left-side 
                     (lbl-superimpose 
                      (refocus 
                       (lbl-superimpose
                        (lt-superimpose (ghost (inset left-side 0 0 (- (pict-width left-side)) 0))
                                        line)
                        var)
                       var))
                     (t "⌋"))]
        [`(/ ,ae1 2)
         (hbl-append (loop #t ae1) (t "/2"))]
        [`(sqr ,ae)
         (define arg (loop #t ae))
         (hbl-append arg (t "²"))] 
        [(? number?) (t (format "~a" ae))]
        [(? symbol-with-no-underscores?)
         (it (format "~a" ae))]
        [`n_1
         (hbl-append (it "n")
                     (basic-text "1" (non-terminal-subscript-style)))]
        [`n_2
         (hbl-append (it "n")
                     (basic-text "2" (non-terminal-subscript-style)))]
        [_ 
         (eprintf "missing ~s\n" ae)
         (blank)])))
  (define (basic-text str style) ((current-text) str style (default-font-size)))

  (define (hline w)
    (dc (λ (dc dx dy) (send dc draw-line dx dy (+ dx w) dy))
        w
        0))
  
  (define (maybe-add-parens add? p)
    (cond
      [add? (hbl-append (t "(") p (t ")"))]
      [else p]))
  
  (define (simple? x) (or (number? x) (symbol? x)))
  
  (define (overline p)
    (define line (inset (hline (pict-width p)) 0 0 0 -2))
    (refocus (vc-append line p) p))
  
  (define (symbol-with-no-underscores? x) 
    (and (symbol? x) (not (regexp-match? #rx"_" (symbol->string x)))))
  (define (t str) (text str))
  (define (it str) (text str '(italic . roman)))
  
  (with-compound-rewriters
   (['@
     (λ (lws)
       (define fn (list-ref lws 1))
       (define enum (list-ref lws 2))
       (define n (list-ref lws 3))
       (define v (list-ref lws 4))
       (define T (list-ref lws 5))
       (list "" enum " @ " n " = " v " | " T ""))]
    ['subst
     (λ (lws)
       (define replace-inside (list-ref lws 2))
       (define x (list-ref lws 3))
       (define new-thing (list-ref lws 4))
       (list "" replace-inside "{" x " := " new-thing "}"))]
    ['⊕
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (list "λx. " arg1 "(x) ∪ " arg2 "(x)"))]
    ['singleton
     (λ (lws)
       (define n1 (list-ref lws 2))
       (define n2 (list-ref lws 3))
       (list "λx. " n1 "=x ? {" n2 "} : ∅"))]
    ['ae-interp
     (λ (lws)
       (list (ae->pict (to-sexp (lw-e (caddr lws))))))]
    ['even
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "" arg " is even"))]
    ['odd
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "" arg " is odd"))]
    ['Eval-enum (λ (lws) (list "" (list-ref lws 2) ""))]
    ['Eval-bij (λ (lws) (list "" (list-ref lws 2) ""))])
   (thunk)))

(define-syntax-rule (w/rewriters e) (w/rewriters/proc (λ () e)))

(define linebreaking-with-cases1
  '(("cons x")
    ("cons y")))

(define linebreaking-with-cases2
  '(("trace" "or l" "or r")
    ("dep" "map" "natural")
    ("ex<" "ex>" "fix")))

(define (semantics-figure)
  (define helv-font "Helvetica")
  (define size 11)
  (parameterize ([label-font-size size]
                 [default-font-size size]
                 [metafunction-font-size size]
                 [metafunction-style helv-font]
                 [literal-style helv-font]
                 [grammar-style helv-font])
    (w/rewriters
     (vc-append
      20
      (ht-append 
       60
       (inset (frame (inset (render-language L #:nts '(e v)) 4)) 4)
       (some-rules linebreaking-with-cases1))
      (some-rules linebreaking-with-cases2)))))

(define (some-rules linebreaking)
  (apply
   vc-append
   20
   (for/list ([line (in-list linebreaking)])
     (apply 
      hb-append
      25
      (for/list ([name (in-list line)])
        (parameterize ([judgment-form-cases (list name)])
          (render-judgment-form @)))))))

(define-syntax-rule 
  (sr e)
  (sr/proc (λ () (render-term L e))))
(define (sr/proc t) 
  (parameterize ([default-font-size 11])
    (w/rewriters
     (t))))

(module+ main 
  (define sf (semantics-figure))
  sf
  (pict-width sf))

(module+ test
  (require rackunit rackunit/log)
  
  (define (n->nn n)
    (define level (integer-sqrt n))
    (define mid-level (/ (- (sqr (+ level 1)) (sqr level) 1) 2))
    (define distance (- n (sqr level)))
    (cond 
      [(< distance mid-level)
       (cons distance level)]
      [else
       (cons level (- distance mid-level))]))
  
  (define (n->nn/e n)
    (:from-nat (:cons/e :natural/e :natural/e) n))
  
  (check-true
   (for/and ([x (in-range 1000)])
     (equal? (n->nn x) (n->nn/e x))))
  
  (define (try-many e)
    (with-handlers ([exn:fail? (λ (x) 
                                 (printf "exn raised while trying ~s\n" e)
                                 (raise x))])
      (for ([x (in-range 1000)])
        (define trial (try-one e x))
        (test-log! trial)
        (unless trial
          (eprintf "try-many: failed for ~s at ~s\n" e x)))))
  
  (check-equal? 
   (:from-nat (term (to-enum (map/e swap-cons swap-cons (cons/e natural/e natural/e))))
              1)
   '(1 . 0))
  (check-equal? 
   (:from-nat (term (to-enum (cons/e natural/e natural/e)))
              1)
   '(0 . 1))

  (check-equal? (term (subst (cons/e natural/e natural/e) x natural/e))
                (term (cons/e natural/e natural/e)))
  (check-equal? (term (subst (cons/e x x) x natural/e))
                (term (cons/e natural/e natural/e)))
  (check-equal? (term (subst (cons/e x (fix/e x x)) x natural/e))
                (term (cons/e natural/e (fix/e x x))))
  (check-equal? (term (subst (cons/e x (fix/e y x)) x natural/e))
                (term (cons/e natural/e (fix/e y natural/e))))
  
  (try-many (term natural/e))
  (try-many (term (or/e natural/e (cons/e natural/e natural/e))))
  (try-many (term (or/e (cons/e natural/e natural/e) natural/e)))
  (try-many (term (cons/e natural/e natural/e)))
  (try-many (term (map/e (swap-zero-with 1) (swap-zero-with 1) natural/e)))
  (try-many (term (map/e swap-cons swap-cons (cons/e natural/e natural/e))))
  (try-many (term (dep/e natural/e nat->map-of-swap-zero-with)))
  (try-many (term (except/e natural/e 1)))
  (try-many (term (fix/e bt (or/e natural/e (cons/e bt bt)))))
  (try-many (term (trace/e 0 natural/e)))
  
  (check-equal? (:enum->list
                 (term (to-enum (map/e (swap-zero-with 3) (swap-zero-with 3) natural/e)))
                 10)
                '(3 1 2 0 4 5 6 7 8 9))
  
  (check-equal? (get-trace (term natural/e) 0) (hash))
  (check-equal? (get-trace (term (trace/e 0 natural/e)) 0) (hash 0 (set 0)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 natural/e)
                                         (trace/e 1 natural/e)))
                           0)
                (hash 1 (set 0) 0 (set 0)))
  (check-equal? (get-trace (term (or/e (trace/e 0 natural/e)
                                       (trace/e 1 (cons/e natural/e natural/e))))
                           100)
                (hash 0 (set 50)))
  (check-equal? (get-trace (term (or/e (trace/e 0 natural/e)
                                       (trace/e 1 (cons/e natural/e natural/e))))
                           101)
                (hash 1 (set 50)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 natural/e)
                                         (cons/e (trace/e 1 natural/e)
                                                 (trace/e 2 natural/e))))
                           100)
                (hash 0 (set 0) 1 (set 1) 2 (set 3)))
  
  ;; test that the dep/e construction is actually not just
  ;; (cons/e natural/e natural/e) but that it shares a lot with it
  (define num-different 0)
  (define num-same 0)
  (for ([x (in-range 100)])
    (define l
      (judgment-holds 
       (@ (dep/e natural/e nat->map-of-swap-zero-with)
          ,x
          v
          T)
       (to-val v)))
    (unless (= 1 (length l))
      (error 'dep/e-test "didn't get singleton back from judgment-holds ~s" l))
    (if (equal? (car l) (:from-nat (:cons/e :natural/e :natural/e) x))
        (set! num-same (+ num-same 1))
        (set! num-different (+ num-different 1))))
  (check-true (> num-same 20))
  (check-true (> num-different 10)))
