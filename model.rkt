#lang racket
(require redex
         pict
         (prefix-in : data/enumerate))

(define-language L
  (e ::= 
     nat/e
     (sum/e e e)
     (cons/e e e))
  (v ::= (cons v v) n)
  (n ::= natural)
  
  (ae ::=
      (+ ae ae) (- ae ae) (/ ae ae) (* ae ae) (- ae ae ae) (integer-sqrt ae) (sqr ae)
      (< ae ae) (>= ae ae)
      n))

(define-judgment-form L
  #:mode (from-nat I I O)
  #:contract (from-nat e natural v)
  
  [--------------------
   (from-nat nat/e n n)]
  
  [(even n) (from-nat e_1 (ae-interp (/ n 2)) v)
   -----------------------------------
   (from-nat (sum/e e_1 e_2) n (cons 0 v))]
  
  [(odd n) (from-nat e_2 (ae-interp (/ (- n 1) 2)) v)
   -----------------------------------
   (from-nat (sum/e e_1 e_2) n (cons 1 v))]
  
  [(side-condition (ae-interp
                    (< (- (+ (* 2 n) 1)
                          (sqr (integer-sqrt n)))
                       (sqr (+ (integer-sqrt n) 1)))))
   (from-nat e_1 (ae-interp (- n (sqr (integer-sqrt n)))) v_1)
   (from-nat e_2 (ae-interp (integer-sqrt n)) v_2)
   --------------------------------------------
   (from-nat (cons/e e_1 e_2) n (cons v_1 v_2))]
  
  [(side-condition (ae-interp
                    (>= (- (+ (* 2 n) 1)
                           (sqr (integer-sqrt n)))
                        (sqr (+ (integer-sqrt n) 1)))))
   (from-nat e_1 (ae-interp (integer-sqrt n)) v_1)
   (from-nat e_2 (ae-interp (- n (sqr (integer-sqrt n)) (/ (- (sqr (+ (integer-sqrt n) 1))
                                                              (sqr (integer-sqrt n))
                                                              1)
                                                           2))) v_2)
   --------------------------------------------
   (from-nat (cons/e e_1 e_2) n (cons v_1 v_2))])

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
  [(to-enum (sum/e e_1 e_2))
   ,(:disj-sum/e (cons (:map/e (λ (x) (cons 0 x))
                               cdr
                               (term (to-enum e_1))) 
                       (λ (x) (equal? (car x) 0)))
                 (cons (:map/e (λ (x) (cons 1 x))
                               cdr
                               (term (to-enum e_2))) 
                       (λ (x) (equal? (car x) 1))))]
  [(to-enum (cons/e e_1 e_2))
   ,(:cons/e (term (to-enum e_1))
             (term (to-enum e_2)))]
  [(to-enum nat/e) ,:nat/e])

(define-metafunction L
  to-val : v -> any
  [(to-val n) n]
  [(to-val (cons v_1 v_2)) ,(cons (term (to-val v_1)) (term (to-val v_2)))])

(define (try-one e n)
  (define enum (term (to-enum ,e)))
  (define ans (judgment-holds (from-nat ,e ,n v) (to-val v)))
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
         (hbl-append (t "√") (overline (t (format "~a" n))))]
        [`(/ ,ae1 2)
         (define numerator (loop #f ae1))
         (define line (frame (blank (+ (pict-width numerator) 4) 0)))
         (vc-append numerator line (t "2"))]
        [`(sqr ,ae)
         (define arg (loop #t ae))
         (hbl-append arg (t "²"))] 
        [(? number?) (t (format "~a" ae))]
        [(? symbol?) 
         ;; need to be using the redex typesetting here....
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
  
  (define (t str) (text str))
  (define (it str) (text str '(italic)))
  
  (with-compound-rewriters
   (['from-nat
     (λ (lws)
       (define fn (list-ref lws 1))
       (define enum (list-ref lws 2))
       (define n (list-ref lws 3))
       (define v (list-ref lws 4))
       (list "" enum " ⊕ " n " = " v ""))]
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
       (list "" arg " is odd"))])
   (thunk)))

(define-syntax-rule (w/rewriters e) (w/rewriters/proc (λ () e)))

(module+ main
  (scale (w/rewriters
          (render-judgment-form from-nat))
         1.5))

(module+ test
  (require rackunit)
  
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
  
  (redex-check L (e n_maybe-too-big) (try-one (term e) (term n_maybe-too-big))))

