#lang racket
(require redex
         pict
         (prefix-in : data/enumerate/lib)
         (prefix-in : data/enumerate/private/unfair))

(provide L
         e? T? v? e/unfair?
         sum-up-to sum-up-to-find-k
         unpair size ae-interp
         @ @<- @*
         to-enum subst to-val)

(define-language L
  (e ::= 
     (below/e n+)
     (or/e e e)
     (cons/e e e)
     (map/e f f e)
     (dep/e fin-or-inf e f)
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
     nat->map-of-swap-zero-with
     nat->below/e-of-that-nat)
  (fin-or-inf ::= fin inf))

(define e? (redex-match L e))
(define T? (redex-match L T))
(define v? (redex-match L v))

(define-judgment-form L
  #:mode (@ I I O O)
  #:contract (@ e natural v T)
  
  [(side-condition (ae-interp (< n n+)))
   ------------------------------------- "below/e"
   (@ (below/e n+) n n ∅)]
  
  [(even n) (side-condition (ae-interp (< n (* (min (size e_1) (size e_2)) 2))))
   (@ e_1 (ae-interp (/ n 2)) v T)
   ---------------------------------------------  "or alt l"
   (@ (or/e e_1 e_2) n (cons 0 v) T)]
  
  [(odd n) (side-condition (ae-interp (< n (* (min (size e_1) (size e_2)) 2))))
   (@ e_2 (ae-interp (/ (- n 1) 2)) v T)
   -------------------------------------------------- "or alt r"
   (@ (or/e e_1 e_2) n (cons 1 v) T)]

  [(side-condition (ae-interp (>= n (* (min (size e_1) (size e_2)) 2)))) (side-condition (ae-interp (< (size e_2) (size e_1))))
   (@ e_1 (ae-interp (- n (size e_2))) v T)
   -------------------------------------------------- "or big l"
   (@ (or/e e_1 e_2) n (cons 0 v) T)]

  [(side-condition (ae-interp (>= n (* (min (size e_1) (size e_2)) 2)))) (side-condition (ae-interp (< (size e_1) (size e_2))))
   (@ e_2 (ae-interp (- n (size e_1))) v T)
   -------------------------------------------------- "or big r"
   (@ (or/e e_1 e_2) n (cons 1 v) T)]

  [(where (× n_1 n_2) (unpair (size e_1) (size e_2) n))
   (@ e_1 n_1 v_1 T_1) (@ e_2 n_2 v_2 T_2)
   ----------------------------------------------------------- "cons"
   (@ (cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))]
  
  [(@ e n v_1 T)
   (where v_2 (Eval-bij (f_1 v_1))) (where v_1 (Eval-bij (f_2 v_2)))
   -----------------------------------------------------------------  "map"
   (@ (map/e f_1 f_2 e) n v_2 T)]
  
  [(@ (cons/e e (below/e ∞)) n_1 (cons v_1 n_2) T_1)
   (@ (Eval-enum (f v_1)) n_2 v_2 T_2) (side-condition (inf? fin-or-inf e f))
   ----------------------------------------------  "dep inf"
   (@ (dep/e fin-or-inf e f) n_1 (cons v_1 v_2) (⊕ T_1 T_2))]

  [;; side-condition has to come before sum-up-to-find-k
   (side-condition (fin? fin-or-inf e f))
   (sum-up-to-find-k n_1 f e n_2)
   (@ e n_2 v_1 T_1) (@ (Eval-enum (f v_1)) (ae-interp (- n_1 (sum-up-to e f n_2))) v_2 T_2)
   ----------------------------------------------  "dep fin"
   (@ (dep/e fin-or-inf e f) n_1 (cons v_1 v_2) (⊕ T_1 T_2))]

  [(@<- e n_1 v_1 T_2)
   (@ e (ae-interp n_2) v_2 T) (side-condition (ae-interp (< n_2 n_1)))
   ---------------------------------------- "ex<"
   (@ (except/e e v_1) n_2 v_2 T)]

  [(@<- e n_1 v_1 T_2)
   (@ e (ae-interp (+ n_2 1)) v_2 T) (side-condition (ae-interp (>= n_2 n_1)))
   ---------------------------------------- "ex≥"
   (@ (except/e e v_1) n_2 v_2 T)]

  [(@ (subst e x (fix/e x e)) n v T)
   --------------------------------- "fix"
   (@ (fix/e x e) n v T)]
  
  [(@ e n_2 v T)
   ----------------------------------------------  "trace"
   (@ (trace/e n_1 e) n_2 v (singleton n_1 n_2))])


;; @, but with the other mode -- we don't model this in Redex
;; instead, just use the implementation in data/enumerate
;; (since we don't need to typeset this direction separately)
(define-judgment-form L
  #:mode (@<- I O I O)
  #:contract (@<- e n v T)
  [(where n ,(:to-nat (term (to-enum e)) (term (to-val v))))
   ---------------------------------------------------------
   (@<- e n v ∅)])

(define-extended-language unfair-L L
  (e ::= .... (unfair-cons/e e e)))

(define-extended-judgment-form unfair-L @
  #:mode (@* I I O O)
  #:contract (@* e natural v T)
  [(unfair-n->n*n n i j) (@* e_1 j v_1 T_1) (@* e_2 i v_2 T_2)
   -----------------------------------------------------------
   (@* (unfair-cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))])

(define-judgment-form unfair-L
  #:mode (unfair-n->n*n I O O)
  [(where (n_x n_y)
          ,(let-values ([(nx ny) (:unfair-n->n*n (term n))])
             (term (,nx ,ny))))
   ----------------------------------------------------------
   (unfair-n->n*n n n_y n_x)])

(define e/unfair? (redex-match unfair-L e))

(define-judgment-form L
  #:mode (sum-up-to-find-k I I I O)
  #:contract (sum-up-to-find-k n f e k)
  [(where k (sum-up-to-find-k/fun n f e))
   --------------------------------------
   (sum-up-to-find-k n f e k)])

(define-metafunction L
  [(sum-up-to-find-k/fun n f e)
   ,(let ([:e (term (to-enum e))])
      (let loop ([k 0]
                 [sum 0])
        (define ith-size (term (size (Eval-enum (f ,(:from-nat :e k))))))
        (cond
          [(and (<= sum (term n)) (< (term n) (+ sum ith-size)))
           k]
          [else
           (loop (+ k 1) (+ sum ith-size))])))])

(define-metafunction L
  size : e -> n+
  [(size (below/e n+)) n+]
  [(size (or/e e_1 e_2)) (ae-interp (+ (size e_1) (size e_2)))]
  [(size (cons/e e_1 e_2)) (ae-interp (* (size e_1) (size e_2)))]
  [(size (map/e f f e)) (size e)]
  [(size (dep/e fin-or-inf e f)) ∞ (side-condition (term (inf? fin-or-inf e f)))]
  [(size (dep/e fin-or-inf e f))
   (ae-interp (* (size e) (sum-all e f)))
   (side-condition (term (ae-interp (< (size e) ∞))))]
  [(size (except/e e v)) (ae-interp (- (size e) 1))]
  [(size (fix/e x e)) ∞]
  [(size (trace/e n e)) (size e)])

(define-metafunction L
  sum-all : e f -> n
  [(sum-all e f) (sum-all/acc 0 e f)])

(define-metafunction L
  sum-all/acc : n e f -> n
  [(sum-all/acc n e f)
   (ae-interp (+ (size (Eval-enum (f v))) (sum-all/acc (ae-interp (+ n 1)) e f)))
   (judgment-holds (@ e n v T))
   (side-condition (term (ae-interp (< n (size e)))))]
  [(sum-all/acc n e f) 0])

(define-metafunction L
  sum-up-to : e f n -> n
  [(sum-up-to e f n)
   (sum-up-to/render f e n)])

(define-metafunction L
  sum-up-to/render : f e n -> n
  [(sum-up-to/render f e n)
   ,(let ([:e (term (to-enum e))])
      (for/sum ([i (in-range (term n))])
        (term (size (Eval-enum (f ,(:from-nat :e i)))))))])

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
  [(Eval-enum (nat->map-of-swap-zero-with n))
   (map/e (swap-zero-with n) (swap-zero-with n) (below/e ∞))]
  [(Eval-enum (nat->below/e-of-that-nat n)) (below/e n)]
  [(Eval-enum (nat->below/e-of-that-nat any)) (below/e 0)]
  [(Eval-enum (f any)) (below/e ∞)])

(define-metafunction L
  inf? : fin-or-inf e f -> boolean
  [(inf? inf e f) #t]
  [(inf? fin e f) #f])
(define-metafunction L
  fin? : fin-or-inf e f -> boolean
  [(fin? inf e f) #f]
  [(fin? fin e f) #t])


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

(define (lift op a b) (if (or (equal? a (term ∞)) (equal? b (term ∞))) (term ∞) (op a b)))
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
    [(equal? a (term ∞)) b]
    [(equal? b (term ∞)) a]
    [else (min a b)]))
(define (</∞ a b) (and (<=/∞ a b) (not (equal? a b))))
(define (>=/∞ a b) (<=/∞ b a))
(define (<=/∞ a b)
  (cond
    [(equal? b (term ∞)) #t]
    [(equal? a (term ∞)) #f]
    [else (<= a b)]))



(define-metafunction unfair-L
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
  [(to-enum (unfair-cons/e e_1 e_2))
   ,(let ([:e1 (term (to-enum e_1))]
          [:e2 (term (to-enum e_2))])
      (:map/e (λ (n)
                (define-values (x y) (:unfair-n->n*n n))
                (cons (:from-nat :e1 x)
                      (:from-nat :e1 y)))
              (λ (pr)
                (:unfair-n*n->n (:to-nat :e1 (car pr))
                                (:to-nat :e2 (cdr pr))))
              :natural/e
              #:contract
              (cons/c (:enum-contract :e1) (:enum-contract :e2))))]
  [(to-enum (below/e ∞)) ,:natural/e]
  [(to-enum (below/e n)) ,(:below/e (term n))]
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
  [(to-enum (dep/e inf e nat->map-of-swap-zero-with))
   ,(:dep/e (term (to-enum e))
            (λ (x)
              (if (exact-nonnegative-integer? x)
                  (term (to-enum (map/e (swap-zero-with ,x) (swap-zero-with ,x) (below/e ∞))))
                  :natural/e)))]
  [(to-enum (dep/e fin e nat->below/e-of-that-nat))
   ,(:dep/e (term (to-enum e))
            (λ (x)
              (if (exact-nonnegative-integer? x)
                  (:below/e x)
                  (:below/e 0)))
            #:f-range-finite? #t)]
  [(to-enum (dep/e inf e any)) (to-enum (cons/e e (below/e ∞)))] ;; should this be an error?
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

