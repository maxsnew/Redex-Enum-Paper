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
     (in/e 0 n+)
     (or/e e e)
     (cons/e e e)
     (map/e f f e)
     (dep/e e f)
     (except/e e v)
     (fix/e x e)
     (trace/e n e)
     x)
  (n+ ::= n ∞)
  (v ::= (cons v v) n)
  (n i j k ::= natural)
  (x ::= variable-not-otherwise-mentioned)
  
  (ae ::=
      (+ ae ae) (/ ae ae) (* ae ae)
      (- ae ae) (- ae ae ae)
      (integer-sqrt ae) (sqr ae)
      (< ae ae) (>= ae ae)
      (min ae ae) (max ae ae)
      (mod ae ae) (div ae ae)
      n+)
  
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
  
  [(side-condition (ae-interp (< n n+)))
   ------------------------------------- "natural"
   (@ (in/e 0 n+) n n ∅)]
  
  [(even n) (@ e_1 (ae-interp (/ n 2)) v T)
   ---------------------------------------------  "or l"
   (@ (or/e e_1 e_2) n (cons 0 v) T)]
  
  [(odd n) (@ e_2 (ae-interp (/ (- n 1) 2)) v T)
   -------------------------------------------------- "or r"
   (@ (or/e e_1 e_2) n (cons 1 v) T)]

  [(where (× n_1 n_2) (unpair (size e_1) (size e_2) n))
   (@ e_1 n_1 v_1 T_1) (@ e_2 n_2 v_2 T_2)
   ----------------------------------------------------------- "cons"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))]
  
  [(@ e n v_1 T)
   (where v_2 (Eval-bij (f_1 v_1))) (where v_1 (Eval-bij (f_2 v_2)))
   -----------------------------------------------------------------  "map"
   (@ (map/e f_1 f_2 e) n v_2 T)]
  
  [(@ (cons/e e (in/e 0 ∞)) n_1 (cons v_1 n_2) T_1)
   (@ (Eval-enum (f v_1)) n_2 v_2 T_2)
   ----------------------------------------------  "dep"
   (@ (dep/e e f) n_1 (cons v_1 v_2) (⊕ T_1 T_2))]

  [(@<- e n_1 v_1 T_2)
   (@ e (ae-interp n_2) v_2 T) (side-condition (ae-interp (< n_2 n_1)))
   ---------------------------------------- "ex<"
   (@ (except/e e v_1) n_2 v_2 T)]

  [(@<- e n_1 v_1 T_2)
   (@ e (ae-interp (+ n_2 1)) v_2 T) (side-condition (ae-interp (>= n_2 n_1)))
   ---------------------------------------- "ex>"
   (@ (except/e e v_1) n_2 v_2 T)]

  [(@ (subst e x (fix/e x e)) n v T)
   --------------------------------- "fix"
   (@ (fix/e x e) n v T)]
  
  [(@ e n_2 v T)
   ----------------------------------------------  "trace"
   (@ (trace/e n_1 e) n_2 v (singleton n_1 n_2))])

;; @, but with the other mode -- we don't model this explicitly,
;; here in Redex, but just use the implementation in data/enumerate
;; (since we don't really want to typeset this separately from the other)
(define-judgment-form L
  #:mode (@<- I O I O)
  #:contract (@<- e n v T)
  [(where n ,(:to-nat (term (to-enum e)) (term (to-val v))))
   ---------------------------------------------------------
   (@<- e n v ∅)])

(define-metafunction L
  size : e -> n+
  [(size (in/e 0 n+)) n+]
  [(size (or/e e_1 e_2)) (ae-interp (+ (size e_1) (size e_2)))]
  [(size (cons/e e_1 e_2)) (ae-interp (* (size e_1) (size e_2)))]
  [(size (map/e f f e)) (size e)]
  [(size (dep/e e f)) ∞]
  [(size (except/e e v)) (ae-interp (- (size e) 1))]
  [(size (fix/e x e)) ∞]
  [(size (trace/e n e)) (size e)])

(define-metafunction L
  unpair : n+ n+ n -> (× n n)
  [(unpair ∞ ∞ n)
   (× (ae-interp (- n (sqr (integer-sqrt n)))) (ae-interp (integer-sqrt n)))
   (side-condition (term (ae-interp (< (- n (sqr (integer-sqrt n)))
                                       (integer-sqrt n)))))]
  [(unpair ∞ ∞ n)
   (× (ae-interp (integer-sqrt n)) (ae-interp (- n (sqr (integer-sqrt n)) (integer-sqrt n))))]
  [(unpair i ∞ n)
   (× (ae-interp (mod n i)) (ae-interp (div n i)))]
  [(unpair ∞ j n)
   (× (ae-interp (div n j)) (ae-interp (mod n j)))]
  [(unpair i j n)
   (× (ae-interp (mod n i)) (ae-interp (div n i)))
   (side-condition (term (ae-interp (< i j))))]
  [(unpair i j n)
   (× (ae-interp (div n j)) (ae-interp (mod n j)))
   (side-condition (term (ae-interp (>= i j))))])

    
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
        [_ (if (equal? e (term x)) (term e_1) e)]))])
 
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
   (map/e (swap-zero-with natural) (swap-zero-with natural) (in/e 0 ∞))]
  [(Eval-enum (f any)) (in/e 0 ∞)])

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
  ae-interp : ae -> n+ or boolean
  [(ae-interp (+ ae_1 ae_2)) ,(+/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (- ae_1 ae_2)) ,(-/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (- ae_1 ae_2 ae_3)) (ae-interp (- ae_1 (+ ae_2 ae_3)))]
  [(ae-interp (/ ae_1 ae_2)) ,(/ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (* ae_1 ae_2)) ,(*/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (< ae_1 ae_2)) ,(</∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (>= ae_1 ae_2)) ,(>=/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (integer-sqrt ae)) ,(integer-sqrt (term (ae-interp ae)))]
  [(ae-interp (sqr ae)) ,(sqr (term (ae-interp ae)))]
  [(ae-interp (div ae_1 ae_2)) ,(floor (/ (term (ae-interp ae_1)) (term (ae-interp ae_2))))]
  [(ae-interp (mod ae_1 ae_2)) ,(modulo (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (min ae_1 ae_2)) ,(min/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp (max ae_1 ae_2)) ,(max/∞ (term (ae-interp ae_1)) (term (ae-interp ae_2)))]
  [(ae-interp n+) n+])

(define (lift op a b) (if (or (equal? a '∞) (equal? b '∞)) a (op a b)))
(define (+/∞ a b) (lift + a b))
(define (-/∞ a b)
  (cond
    [(and (equal? a '∞) (not (equal? b '∞))) a]
    [(and (number? a) (number? b)) (- a b)]
    [else (error '- "cannot subtract: ~s - ~s" a b)]))
(define (*/∞ a b) (lift * a b))
(define (max/∞ a b) (lift max a b))
(define (min/∞ a b)
  (cond
    [(equal? a '∞) b]
    [(equal? b '∞) a]
    [else (min a b)]))
(define (</∞ a b) (and (<=/∞ a b) (not (equal? a b))))
(define (>=/∞ a b) (<=/∞ b a))
(define (<=/∞ a b)
  (cond
    [(equal? b '∞) #t]
    [(equal? a '∞) #f]
    [else (<= a b)]))

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
  [(to-enum (in/e 0 ∞)) ,:natural/e]
  [(to-enum (in/e 0 n)) ,(:below/e (term n))]
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
                  (term (to-enum (map/e (swap-zero-with ,x) (swap-zero-with ,x) (in/e 0 ∞))))
                  :natural/e)))]
  [(to-enum (dep/e e any)) (to-enum (cons/e e (in/e 0 ∞)))]
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
        [`(* ,ae1 ,ae2)
         (htl-append (loop #t ae1)
                     (t "·")
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
        [`(div ,ae1 ,ae2)
         (hbl-append
          (t "⌊")
          (loop #t ae1)
          (t "/")
          (loop #t ae2)
          (t "⌋"))]
        [`(mod ,ae1 ,ae2)
         (hbl-append
          (loop #t ae1)
          (t "%")
          (loop #t ae2))]
        [`(sqr ,ae)
         (define arg (loop #t ae))
         (hbl-append arg (t "²"))]
        [`(size ,ae)
         (define arg (loop #f ae))
         (hbl-append (t "‖") arg (t "‖"))]
        [(? number?) (t (format "~a" ae))]
        [(? symbol-with-no-underscores?)
         (it (format "~a" ae))]
        [`n_1
         (hbl-append (it "n")
                     (basic-text "1" (non-terminal-subscript-style)))]
        [`n_2
         (hbl-append (it "n")
                     (basic-text "2" (non-terminal-subscript-style)))]
        [`e_1
         (hbl-append (it "e")
                     (basic-text "1" (non-terminal-subscript-style)))]
        [`e_2
         (hbl-append (it "e")
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

  (define (@-rewrite lws)
    (define fn (list-ref lws 1))
    (define enum (list-ref lws 2))
    (define n (list-ref lws 3))
    (define v (list-ref lws 4))
    (define T (list-ref lws 5))
    (list "" enum " @ " n " = " v " | " T ""))
  
  (with-compound-rewriters
   (['@ @-rewrite]
    ['@<- @-rewrite]
    ['subst
     (λ (lws)
       (define replace-inside (list-ref lws 2))
       (define x (list-ref lws 3))
       (define new-thing (list-ref lws 4))
       (list "" replace-inside "{" x " := " new-thing "}"))]
    ['×
     (λ (lws)
       (list "⟨" (list-ref lws 2) ", " (list-ref lws 3) "⟩"))]
    ['size
     (λ (lws)
       (list "‖" (list-ref lws 2) "‖"))]
    ['unpair
     (λ (lws)
       (list "unpair(" (list-ref lws 2) ", " (list-ref lws 3) ", " (list-ref lws 4) ")"))]
    ['in/e
     (λ (lws)
       (list "[0," (list-ref lws 3) ")"))]
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
  '(("cons")))

(define linebreaking-with-cases2
  '(("trace" "or l" "or r")
    ("dep" "map" "natural")
    ("ex<" "ex>" "fix")))

(define (semantics-figure)
  (define helv-font "Helvetica")
  (define font-size 11)
  (parameterize ([label-font-size font-size]
                 [default-font-size font-size]
                 [metafunction-font-size font-size]
                 [metafunction-style helv-font]
                 [literal-style helv-font]
                 [grammar-style helv-font])
    (w/rewriters
     (vc-append
      20
      (ht-append 
       60
       (inset (frame (inset (render-language L #:nts '(e n+ v)) 4)) 4)
       (some-rules linebreaking-with-cases1))
      (some-rules linebreaking-with-cases2)
      (hc-append (render-metafunction unpair)
                 (render-metafunction size))))))

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
    (let/ec k
      (with-handlers ([exn:fail? (λ (x) 
                                   (printf "exn raised while trying ~s\n" e)
                                   (raise x))])
        (define failures 0)
        (for ([x (in-range (term (ae-interp (min (size ,e) 1000))))])
          (define trial (try-one e x))
          (test-log! trial)
          (unless trial
            (set! failures (+ failures 1))
            (eprintf "try-many: failed for ~s at ~s\n" e x)
            (when (> failures 5)
              (k (void))))))))

  (check-equal? (term (ae-interp (+ 1 2))) 3)
  (check-equal? (term (ae-interp (< 1 2))) #t)
  (check-equal? (term (ae-interp (< 1 1))) #f)
  (check-equal? (term (ae-interp (< 2 1))) #f)
  (check-equal? (term (ae-interp (>= 1 2))) #f)
  (check-equal? (term (ae-interp (>= 1 1))) #t)
  (check-equal? (term (ae-interp (>= 2 1))) #t)
  (check-equal? (term (ae-interp (- 11 4))) 7)
  (check-equal? (term (ae-interp (+ 11 4))) 15)
  (check-equal? (term (ae-interp (* 11 4))) 44)
  (check-equal? (term (ae-interp (/ 12 4))) 3)
  (check-equal? (term (ae-interp (mod 12 5))) 2)
  (check-equal? (term (ae-interp (div 12 7))) 1)

  (check-equal? (term (size (in/e 0 2))) 2)
  (check-equal? (term (size (in/e 0 ∞))) (term ∞))
  (check-equal? (term (size (cons/e (in/e 0 ∞) (in/e 0 11)))) (term ∞))
  (check-equal? (term (size (cons/e (in/e 0 4) (in/e 0 11)))) 44)
  (check-equal? (term (size (or/e (in/e 0 4) (in/e 0 11)))) 15)
  (check-equal? (term (size (dep/e (in/e 0 ∞) nat->map-of-swap-zero-with))) (term ∞))
  (check-equal? (term (size (except/e (in/e 0 10) 3))) 9)
  (check-equal? (term (size (except/e (in/e 0 ∞) 3))) (term ∞))
  ;; this is not a good test case...
  (check-equal? (term (size (fix/e x (in/e 0 ∞)))) (term ∞))
                
  (check-equal? 
   (:from-nat (term (to-enum (map/e swap-cons swap-cons (cons/e (in/e 0 ∞) (in/e 0 ∞)))))
              1)
   '(1 . 0))
  (check-equal? 
   (:from-nat (term (to-enum (cons/e (in/e 0 ∞) (in/e 0 ∞))))
              1)
   '(0 . 1))

  (check-equal? (term (subst (cons/e (in/e 0 ∞) (in/e 0 ∞)) x (in/e 0 ∞)))
                (term (cons/e (in/e 0 ∞) (in/e 0 ∞))))
  (check-equal? (term (subst (cons/e x x) x (in/e 0 ∞)))
                (term (cons/e (in/e 0 ∞) (in/e 0 ∞))))
  (check-equal? (term (subst (cons/e x (fix/e x x)) x (in/e 0 ∞)))
                (term (cons/e (in/e 0 ∞) (fix/e x x))))
  (check-equal? (term (subst (cons/e x (fix/e y x)) x (in/e 0 ∞)))
                (term (cons/e (in/e 0 ∞) (fix/e y (in/e 0 ∞)))))

  (check-equal? (judgment-holds (@<- (cons/e (in/e 0 ∞) (in/e 0 ∞)) n (cons 0 0) T) n)
                '(0))
  (check-equal? (judgment-holds (@<- (cons/e (in/e 0 ∞) (in/e 0 ∞)) n (cons 3 4) T) n)
                (list (:to-nat (:cons/e :natural/e :natural/e) (cons 3 4))))
  
  (try-many (term (in/e 0 ∞)))
  (try-many (term (or/e (in/e 0 ∞) (cons/e (in/e 0 ∞) (in/e 0 ∞)))))
  (try-many (term (or/e (cons/e (in/e 0 ∞) (in/e 0 ∞)) (in/e 0 ∞))))
  (try-many (term (cons/e (in/e 0 ∞) (in/e 0 ∞))))
  (try-many (term (map/e (swap-zero-with 1) (swap-zero-with 1) (in/e 0 ∞))))
  (try-many (term (map/e swap-cons swap-cons (cons/e (in/e 0 ∞) (in/e 0 ∞)))))
  (try-many (term (dep/e (in/e 0 ∞) nat->map-of-swap-zero-with)))
  (try-many (term (except/e (in/e 0 ∞) 1)))
  (try-many (term (fix/e bt (or/e (in/e 0 ∞) (cons/e bt bt)))))
  (try-many (term (trace/e 0 (in/e 0 ∞))))
  (try-many (term (cons/e (in/e 0 3) (in/e 0 ∞))))
  (try-many (term (cons/e (in/e 0 ∞) (in/e 0 3))))
  (try-many (term (cons/e (in/e 0 3) (in/e 0 5))))
  (try-many (term (cons/e (in/e 0 3) (in/e 0 2))))
 
  (check-equal? (:enum->list
                 (term (to-enum (map/e (swap-zero-with 3) (swap-zero-with 3) (in/e 0 ∞))))
                 10)
                '(3 1 2 0 4 5 6 7 8 9))
  
  (check-equal? (get-trace (term (in/e 0 ∞)) 0) (hash))
  (check-equal? (get-trace (term (trace/e 0 (in/e 0 ∞))) 0) (hash 0 (set 0)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 (in/e 0 ∞))
                                         (trace/e 1 (in/e 0 ∞))))
                           0)
                (hash 1 (set 0) 0 (set 0)))
  (check-equal? (get-trace (term (or/e (trace/e 0 (in/e 0 ∞))
                                       (trace/e 1 (cons/e (in/e 0 ∞) (in/e 0 ∞)))))
                           100)
                (hash 0 (set 50)))
  (check-equal? (get-trace (term (or/e (trace/e 0 (in/e 0 ∞))
                                       (trace/e 1 (cons/e (in/e 0 ∞) (in/e 0 ∞)))))
                           101)
                (hash 1 (set 50)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 (in/e 0 ∞))
                                         (cons/e (trace/e 1 (in/e 0 ∞))
                                                 (trace/e 2 (in/e 0 ∞)))))
                           100)
                (hash 0 (set 0) 1 (set 1) 2 (set 3)))
  
  ;; test that the dep/e construction is actually not just
  ;; (cons/e (in/e 0 ∞) (in/e 0 ∞)) but that it shares a lot with it
  (define num-different 0)
  (define num-same 0)
  (for ([x (in-range 100)])
    (define l
      (judgment-holds 
       (@ (dep/e (in/e 0 ∞) nat->map-of-swap-zero-with)
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
