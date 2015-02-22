#lang racket
(require redex
         pict
         (prefix-in : data/enumerate/lib))

(provide semantics-figure sr L)

(define-language L
  (e ::= 
     nat/e
     (or/e e e)
     (cons/e e e)
     (map/e f f e)
     (dep/e e f)
     (trace/e n e))
  (v ::= (cons v v) n)
  (n ::= integer)
  
  (ae ::=
      (+ ae ae) (- ae ae) (/ ae ae) (* ae ae) (- ae ae ae) (integer-sqrt ae) (sqr ae)
      (< ae ae) (>= ae ae)
      n)
  
  (T ::= ∅ (n ↦ (n n ...) T))
  
  (f ::= 
     (add integer)
     (mult natural)
     (mult (/ natural))
     produce-map/e-nat/e-with-add-of-given-int))

(define-judgment-form L
  #:mode (@ I I O O)
  #:contract (@ e natural v T)
  
  [-------------------- "nat/e"
   (@ nat/e n n ∅)]
  
  [(even n) (@ e_1 (ae-interp (/ n 2)) v T)
   ---------------------------------------------  "or l"
   (@ (or/e e_1 e_2) n (cons 0 v) T)]
  
  [(odd n) (@ e_2 (ae-interp (/ (- n 1) 2)) v T)
   -------------------------------------------------- "or r"
   (@ (or/e e_1 e_2) n (cons 1 v) T)]
  
  [(side-condition (ae-interp
                    (< (- (+ (* 2 n) 1)
                          (sqr (integer-sqrt n)))
                       (sqr (+ (integer-sqrt n) 1))))) (@ e_1 (ae-interp (- n (sqr (integer-sqrt n)))) v_1 T_1)
   (@ e_2 (ae-interp (integer-sqrt n)) v_2 T_2)
   ----------------------------------------------------------- "cons/e x"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (∪ T_1 T_2))]
  
  [(side-condition (ae-interp
                    (>= (- (+ (* 2 n) 1)
                           (sqr (integer-sqrt n)))
                        (sqr (+ (integer-sqrt n) 1))))) (@ e_1 (ae-interp (integer-sqrt n)) v_1 T_1)
   (@ e_2 (ae-interp (- n (sqr (integer-sqrt n)) (/ (- (sqr (+ (integer-sqrt n) 1))
                                                              (sqr (integer-sqrt n))
                                                              1)
                                                           2))) v_2 T_2)
   ---------------------------------------------------------------------------------------- "cons/e y"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (∪ T_1 T_2))]
  
  
  [(@ e n v T)
   -------------------------------------------------  "map in"
   (@ (map/e f_1 f_2 e) n (Eval-num (f_1 v)) T)]
  
  [(@ e n (Eval-num (f_2 v)) T)
   ---------------------------------  "map out"
   (@ (map/e f_1 f_2 e) n v T)]
  
  [(@ (cons/e e nat/e) n_1 (cons v_1 n_2) T_1)
   (@ (Eval-enum (f v_1)) n_2 v_2 T_2)
   ----------------------------------------------  "dep/e"
   (@ (dep/e e f) n_1 (cons v_1 v_2) (∪ T_1 T_2))]
  
  [(@ e n_2 v T)
   ----------------------------------------------  "trace/e"
   (@ (trace/e n_1 e) n_2 v (singleton n_1 n_2))])

(define-metafunction L
  ∪ : T T -> T
  [(∪ ∅ T) T]
  [(∪ (n_1 ↦ (n_2 ...) T_1) T_2) (∪ T_1 (join n_1 (n_2 ...) T_2))])

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
  Eval-num : (f any) -> any
  [(Eval-num ((add integer) n)) ,(+ (term integer) (term n))]
  [(Eval-num ((mult natural) n)) ,(* (term natural) (term n))]
  [(Eval-num ((mult (/ natural)) n)) ,(* (/ (term natural)) (term n))]
  [(Eval-num (f any)) any])

(define-metafunction L
  Eval-enum : (f any) -> any
  [(Eval-enum (produce-map/e-nat/e-with-add-of-given-int integer))
   (map/e (add integer) (add ,(- (term integer))) nat/e)]
  [(Eval-enum (f any)) nat/e])

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
  [(to-enum nat/e) ,:nat/e]
  
  ;; these don't handle all of the cases, but instead
  ;; collapse into less interesting enumerations when
  ;; we step outside of the useful area.
  [(to-enum (map/e (add integer) any e))
   ,(let ([e (term (to-enum e))])
      (:map/e (λ (x) (if (integer? x) (+ x (term integer)) x))
              (λ (x) (if (integer? x) (- x (term integer)) x))
              e
              #:contract (or/c (and/c exact-integer? (>=/c (term integer)))
                               (:enum-contract e))))]
  [(to-enum (map/e (mult any) any e))
   ,(let ([e (term (to-enum e))]
          [factor (if (pair? (term any))
                      (/ (second (term any)))
                      (term any))])
      (:map/e (λ (x) (if (integer? x) (* x factor) x))
              (λ (x) (if (integer? x) (/ x factor) x))
              e
              #:contract (or/c rational?
                               (:enum-contract e))))]
  [(to-enum (map/e any any e)) (to-enum e)]
  [(to-enum (dep/e e produce-map/e-nat/e-with-add-of-given-int))
   ,(:dep/e (term (to-enum e))
            (λ (x) 
              (if (integer? x)
                  (:map/e (λ (y) (+ y x)) (λ (y) (- y x)) :nat/e
                          #:contract (and/c exact-integer? (>=/c x)))
                  :nat/e)))]
  [(to-enum (dep/e e any)) (to-enum (cons/e e nat/e))]
  [(to-enum (trace/e n e)) (to-enum e)])

(define-metafunction L
  to-val : v -> any
  [(to-val n) n]
  [(to-val (cons v_1 v_2)) ,(cons (term (to-val v_1)) (term (to-val v_2)))])

(define (try-one e n)
  (define enum (term (to-enum ,e)))
  (define ans (judgment-holds (@ ,e ,n v T) (to-val v)))
  (and (pair? ans) 
       (null? (cdr ans))
       (equal? (car ans) (:from-nat enum n))))

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
        [_ 
         (eprintf "missing ~s\n" ae)
         (blank)])))
  
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
    ['∪
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (list "" arg1 " ∪ " arg2 ""))]
    ['singleton
     (λ (lws)
       (define n1 (list-ref lws 2))
       (define n2 (list-ref lws 3))
       (list "{" n1 " ↦ {" n2 "}}"))]
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
    ['Eval-num (λ (lws) (list "" (list-ref lws 2) ""))])
   (thunk)))

(define-syntax-rule (w/rewriters e) (w/rewriters/proc (λ () e)))

(define linebreaking-with-cases
  '(("or l" "or r")
    ("cons/e x")
    ("cons/e y")
    ("map in" "map out")
    ("nat/e" "dep/e")
    ("trace/e")))

(define (semantics-figure)
  (w/rewriters
   (ht-append
    40
    (inset (frame (inset (render-language L #:nts '(e)) 4)) 4)
    (apply
     vc-append
     20
     (for/list ([line (in-list linebreaking-with-cases)])
       (apply 
        hb-append
        30
        (for/list ([name (in-list line)])
          (parameterize ([judgment-form-cases (list name)])
            (render-judgment-form @)))))))))

(define-syntax-rule 
  (sr e)
  (sr/proc (λ () (render-term L e))))
(define (sr/proc t) 
  (parameterize ([default-font-size 11])
    (w/rewriters
     (t))))

(module+ main (semantics-figure))

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
    (:from-nat (:cons/e :nat/e :nat/e) n))
  
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
  
  (try-many (term nat/e))
  (try-many (term (or/e nat/e (cons/e nat/e nat/e))))
  (try-many (term (or/e (cons/e nat/e nat/e) nat/e)))
  (try-many (term (cons/e nat/e nat/e)))
  (try-many (term (map/e (add 1) (add -1) nat/e)))
  (try-many (term (dep/e nat/e produce-map/e-nat/e-with-add-of-given-int)))
  (try-many (term (trace/e 0 nat/e)))
  
  (define (get-trace e i)
    (define trs (judgment-holds (@ ,e ,i v T) T))
    (unless (and (pair? trs) (= 1 (length trs)))
      (error 'get-trace "got bad judgment-form result ~s" trs))
    (define ht (make-hash))
    (let loop ([T (car trs)])
      (match T
        [`∅ (hash)]
        [`(,n1 ↦ (,n2 ...) ,T)
         (when (hash-ref ht n1 #f)
           (error 'get-trace "got multiple mappings of ~a for ~s" n1 e))
         (unless (equal? (remove-duplicates n2) n2)
           (error 'get-trace "not a set @ ~a for ~s" n1 e))
         (hash-set (loop T) n1 (apply set n2))])))
  
  (check-equal? (get-trace (term nat/e) 0) (hash))
  (check-equal? (get-trace (term (trace/e 0 nat/e)) 0) (hash 0 (set 0)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 nat/e)
                                         (trace/e 1 nat/e)))
                           0)
                (hash 1 (set 0) 0 (set 0)))
  (check-equal? (get-trace (term (or/e (trace/e 0 nat/e)
                                       (trace/e 1 (cons/e nat/e nat/e))))
                           100)
                (hash 0 (set 50)))
  (check-equal? (get-trace (term (or/e (trace/e 0 nat/e)
                                       (trace/e 1 (cons/e nat/e nat/e))))
                           101)
                (hash 1 (set 50)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 nat/e)
                                         (cons/e (trace/e 1 nat/e)
                                                 (trace/e 2 nat/e))))
                           100)
                (hash 0 (set 0) 1 (set 1) 2 (set 3)))
  
  ;; test dep/e
  (for ([x (in-range 1000)])
    (define l
      (judgment-holds 
       (@ (dep/e nat/e produce-map/e-nat/e-with-add-of-given-int)
          ,x
          v
          T)
       (to-val v)))
    (define passes (and (pair? l)
                        (null? (cdr l))
                        (let ([enum-value (car l)])
                          (<= (car enum-value) (cdr enum-value)))))
    (test-log! passes)
    (unless passes
      (eprintf "dep/e test failes for ~s, got ~s\n" x l)))
  
  ;; test we can recombine and get nats back
  (for ([x (in-range 1000)])
    (define l
      (judgment-holds 
       (@ (or/e (map/e (mult 2) (mult (/ 2)) nat/e)
                (map/e (add 1) (add -1) (map/e (mult 2) (mult (/ 2)) nat/e)))
          ,x
          v
          T)
       (to-val v)))
    (define n (and (pair? l) 
                   (null? (cdr l))
                   ;; above checks we got one result from the judgment
                   (let ([v (car l)])
                     ;; here we drop the or/e injection
                     (cdr v))))
    (define passed? (equal? n x))
    (test-log! passed?)
    (unless passed?
      (eprintf "nat/e recombination didn't work for ~s, got ~s" x l))))