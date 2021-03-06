#lang racket
(require redex
         pict
         (prefix-in : data/enumerate/lib/unsafe)
         (prefix-in : data/enumerate/private/unfair))

(provide L
         e? T? v?
         sum-up-to sum-up-to-find-k
         unpair size ae-interp
         @ @<- ⊢v ty tye
         to-enum subst-τ subst-e to-val)

(define-language L
  (e ::= 
     (below/e n+)
     (or/e e e)
     (cons/e e e)
     (unfair-cons/e e e)
     (map/e f f e)
     (dep/e fin-or-inf e f)
     (except/e e v)
     (fix/e x e)
     (trace/e n e)
     x)
  (n+ ::= n ∞)
  (τ ::= n+ (∧ τ τ) (∨ τ τ) 
     (μ x τ) x (- τ v))
  (v ::=
     (inl v) (inr v)
     (cons v v) n)
  (n i j k ::= natural)
  (x ::= variable-not-otherwise-mentioned)
  (Γ ::= (x ...))
  
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
     (swap-zero-with n)
     (nat->map-of-swap-zero-with n+)
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
   (@ (or/e e_1 e_2) n (inl v) T)]
  
  [(odd n) (side-condition (ae-interp (< n (* (min (size e_1) (size e_2)) 2))))
   (@ e_2 (ae-interp (/ (- n 1) 2)) v T)
   -------------------------------------------------- "or alt r"
   (@ (or/e e_1 e_2) n (inr v) T)]

  [(side-condition (ae-interp (>= n (* (min (size e_1) (size e_2)) 2)))) (side-condition (ae-interp (< (size e_2) (size e_1))))
   (@ e_1 (ae-interp (- n (size e_2))) v T)
   -------------------------------------------------- "or big l"
   (@ (or/e e_1 e_2) n (inl v) T)]

  [(side-condition (ae-interp (>= n (* (min (size e_1) (size e_2)) 2)))) (side-condition (ae-interp (< (size e_1) (size e_2))))
   (@ e_2 (ae-interp (- n (size e_1))) v T)
   -------------------------------------------------- "or big r"
   (@ (or/e e_1 e_2) n (inr v) T)]

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

  [(@ (subst-e e x (fix/e x e)) n v T)
   --------------------------------- "fix"
   (@ (fix/e x e) n v T)]
  
  [(@ e n_2 v T)
   ----------------------------------------------  "trace"
   (@ (trace/e n_1 e) n_2 v (singleton n_1 n_2))]

  [(unfair-n->n*n n i j) (@ e_1 j v_1 T_1) (@ e_2 i v_2 T_2)
   ----------------------------------------------------------- "unfair"
   (@ (unfair-cons/e e_1 e_2) n (cons v_1 v_2) (⊕ T_1 T_2))])


;; @, but with the other mode -- we don't model this in Redex
;; instead, just use the implementation in data/enumerate
;; (since we don't need to typeset this direction separately)
(define-judgment-form L
  #:mode (@<- I O I O)
  #:contract (@<- e n v T)
  [(where n ,(:to-nat (term (to-enum e)) (term (to-val v))))
   ---------------------------------------------------------
   (@<- e n v ∅)])

(define-judgment-form L
  #:mode (unfair-n->n*n I O O)
  [(where (n_x n_y)
          ,(let-values ([(nx ny) (:unfair-n->n*n (term n))])
             (term (,nx ,ny))))
   ----------------------------------------------------------
   (unfair-n->n*n n n_y n_x)])

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

;; assumes closed expressions/types
(define-metafunction L
  subst-e : e x e -> e
  [(subst-e e_2 x e_1)
   ,(do-subst (term e_2) (term x) (term e_1))])

(define-metafunction L
  subst-τ : τ x τ -> τ
  [(subst-τ τ_2 x τ_1)
   ,(do-subst (term τ_2) (term x) (term τ_1))])

(define (do-subst e2 x e1)
  (let loop ([e e2])
    (match e
      [`(,(or 'fix/e 'μ) ,x2 ,e-body)
       (define kwd (car e))
       (if (equal? x2 x)
           `(,kwd ,x2 ,e-body)
           `(,kwd ,x2 ,(loop e-body)))]
      [(? list?) (map loop e)]
      [_ (if (equal? e x) e1 e)])))
 
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
  [(Eval-enum ((nat->map-of-swap-zero-with n+) n))
   (map/e (swap-zero-with n) (swap-zero-with n) (below/e n+))]
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

(define-metafunction L
  size : e -> n+
  [(size (below/e n+)) n+]
  [(size (or/e e_1 e_2)) (ae-interp (+ (size e_1) (size e_2)))]
  [(size (cons/e e_1 e_2)) (ae-interp (* (size e_1) (size e_2)))]
  [(size (unfair-cons/e e_1 e_2)) (ae-interp (* (size e_1) (size e_2)))]
  [(size (map/e f f e)) (size e)]
  [(size (dep/e fin-or-inf e f)) ∞ (side-condition (term (inf? fin-or-inf e f)))]
  [(size (dep/e fin-or-inf e f))
   (ae-interp (* (size e) (sum-all e f)))
   (side-condition (term (ae-interp (< (size e) ∞))))]
  [(size (except/e e v)) (ae-interp (- (size e) 1))]
  [(size (fix/e x e))
   (size e)
   (side-condition (term (same (subst-e e x (fix/e x e)) e)))]
  [(size (fix/e x e)) ∞]
  [(size (trace/e n e)) (size e)])

(define-metafunction L
  [(ty e) (tye (empty-set) e)])
(define-metafunction L
  [(tye Γ (below/e n+)) n+]
  [(tye Γ (or/e e_1 e_2)) (∨ (tye Γ e_1) (tye Γ e_2))]
  [(tye Γ (cons/e e_1 e_2)) (∧ (tye Γ e_1) (tye Γ e_2))]
  [(tye Γ (unfair-cons/e e_1 e_2)) (∧ (tye Γ e_1) (tye Γ e_2))]
  [(tye Γ (map/e f_1 f_2 e))
   (rng f_1)
   (side-condition (term (same (tye Γ e) (rng f_2))))]
  [(tye Γ (dep/e fin-or-inf e f)) (∧ (tye Γ e) (rng f))]
  [(tye Γ (except/e e v)) (- (tye Γ e) v)]
  [(tye Γ (fix/e x e)) (μ x (tye (extend Γ x) e))]
  [(tye Γ (trace/e n e)) (tye Γ e)]
  [(tye Γ x) x (side-condition (term (contains x Γ)))])

(define-metafunction L
  rng : f -> τ
  [(rng swap-cons) (∧ ∞ ∞)]
  [(rng (swap-zero-with n)) ∞]
  [(rng (nat->map-of-swap-zero-with n+)) n+])

(define-metafunction L
  contains : x Γ -> boolean
  [(contains x_1 (x_2 ... x_1 x_3 ...)) #t]
  [(contains x_1 (x_2 ...)) #f])

(define-metafunction L
  extend : Γ x -> Γ
  [(extend (x_1 ...) x_2) (x_2 x_1 ...)])

(define-metafunction L
  empty-set : -> Γ
  [(empty-set) ()])

(define-judgment-form L
  #:mode (⊢v I I)
  #:contract (⊢v v τ)

  [(side-condition (ae-interp (< n n+)))
   --------------------
   (⊢v n n+)]

  [(⊢v v_1 τ_1) (⊢v v_2 τ_2)
   -------------------------------
   (⊢v (cons v_1 v_2) (∧ τ_1 τ_2))]

  [(⊢v v (subst-τ τ x (μ x τ)))
   --------------------------
   (⊢v v (μ x τ))]

  [(⊢v v τ_2)
   ------------------------
   (⊢v (inr v) (∨ τ_1 τ_2))]

  [(⊢v v τ_1)
   ------------------------
   (⊢v (inl v) (∨ τ_1 τ_2))]

  [(⊢v v_1 τ_1) (side-condition (different v_1 v_2))
   -------------------------------------------------
   (⊢v v_1 (- τ_1 v_2))])

(define-metafunction L
  same : any any -> boolean
  [(same any_1 any_1) #t]
  [(same any_1 any_2) #f])

(define-metafunction L
  different : any any -> boolean
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(define-metafunction L
  to-enum : e -> (side-condition any_1 (:enum? (term any_1)))
  [(to-enum e) any_1 (where (any_1 any_2) (to-enum+ctc e))])

(define-metafunction L
  to-enum+ctc : e -> ((side-condition any_1 (:enum? (term any_1)))
                      (side-condition any_2 (contract? (term any_2))))
  [(to-enum+ctc (or/e e_1 e_2))
   ,(match-let ([(list :e1 c1) (term (to-enum+ctc e_1))]
                [(list :e2 c2) (term (to-enum+ctc e_2))])
      (define a
        (:map/e (λ (x) (cons 0 x))
                cdr
                :e1
                #:contract (cons/c 0 c1)))
      (define b
        (:map/e (λ (x) (cons 1 x))
                cdr
                :e2
                #:contract (cons/c 1 c2)))
      (list (:or/e a b)
            (or/c (cons/c 0 c1) (cons/c 1 c2))))]
  [(to-enum+ctc (cons/e e_1 e_2))
   ,(match-let ([(list e1 c1) (term (to-enum+ctc e_1))]
                [(list e2 c2) (term (to-enum+ctc e_2))])
      (list (:cons/e e1 e2)
            (cons/c c1 c2)))]
  [(to-enum+ctc (unfair-cons/e e_1 e_2))
   ,(match-let ([(list :e1 c1) (term (to-enum+ctc e_1))]
                [(list :e2 c2) (term (to-enum+ctc e_2))])
      (list (:map/e (λ (n)
                      (define-values (x y) (:unfair-n->n*n n))
                      (cons (:from-nat :e1 x)
                            (:from-nat :e1 y)))
                    (λ (pr)
                      (:unfair-n*n->n (:to-nat :e1 (car pr))
                                      (:to-nat :e2 (cdr pr))))
                    :natural/e
                    #:contract
                    (cons/c c1 c2))
            (cons/c c1 c2)))]
  [(to-enum+ctc (below/e ∞)) ,(let ([:e :natural/e])
                                (list :e (:enum-contract :e)))]
  [(to-enum+ctc (below/e n)) ,(let ([:e (:below/e (term n))])
                                (list :e (:enum-contract :e)))]
  [(to-enum+ctc (map/e (swap-zero-with natural) (swap-zero-with natural) e))
   ,(match-let ([(list :e c) (term (to-enum+ctc e))]
                [swapper
                 (λ (x) (if (natural? x)
                            (cond
                              [(= x (term natural)) 0]
                              [(= x 0) (term natural)]
                              [else x])
                            x))])
      (list (:map/e swapper swapper :e #:contract c)
            c))]
  [(to-enum+ctc (map/e swap-cons swap-cons e))
   ,(match-let ([(list :e c) (term (to-enum+ctc e))]
                [swap (λ (x) (if (pair? x) (cons (cdr x) (car x)) x))])
      (list (:map/e swap swap :e #:contract c) c))]
  [(to-enum+ctc (map/e any any e)) (to-enum+ctc e)]
  [(to-enum+ctc (dep/e inf e (nat->map-of-swap-zero-with n+)))
   ,(match-let ([(list :e c) (term (to-enum+ctc e))])
      (list (:dep/e :e
                    (λ (x)
                      (if (natural? x)
                          (term (to-enum (map/e (swap-zero-with ,x) (swap-zero-with ,x) (below/e n+))))
                          :natural/e)))
            (cons/c natural? natural?)))]
  [(to-enum+ctc (dep/e fin e nat->below/e-of-that-nat))
   ,(match-let ([(list :e c) (term (to-enum+ctc e))])
      (list (:dep/e :e
                    (λ (x)
                      (if (natural? x)
                          (:below/e x)
                          (:below/e 0)))
                    #:f-range-finite? #t)
            (cons/dc [hd natural?]
                     [tl (hd) (and/c exact-integer? (</c hd))])))]
  [(to-enum+ctc (dep/e inf e any)) (to-enum+ctc (cons/e e (below/e ∞)))] ;; should this be an error?
  [(to-enum+ctc (except/e e n))
   ,(match-let ([(list :e c) (term (to-enum+ctc e))])
      (list (:except/e :e (:from-nat :e (term n)))
            (and/c c (λ (x) (not (equal? x (term n)))))))]
  [(to-enum+ctc (fix/e x e))
   ,(match-letrec ([:e (:delay/e (list-ref converted-e 0))]
                   [c (recursive-contract (list-ref converted-e 1) #:flat)]
                   [converted-e
                    (begin
                      (parameterize ([e-env (hash-set (e-env) (term x) :e)]
                                     [c-env (hash-set (c-env) (term x) c)])
                        (term (to-enum+ctc e))))])
      converted-e)]
  [(to-enum+ctc x)
   ,(list (hash-ref (e-env) (term x))
          (hash-ref (c-env) (term x)))]
  [(to-enum+ctc (trace/e n e)) (to-enum+ctc e)])

(define e-env (make-parameter (hash)))
(define c-env (make-parameter (hash)))

(define-metafunction L
  to-val : v -> any
  [(to-val n) n]
  [(to-val (inl v)) ,(cons 0 (term (to-val v)))]
  [(to-val (inr v)) ,(cons 1 (term (to-val v)))]
  [(to-val (cons v_1 v_2)) ,(cons (term (to-val v_1)) (term (to-val v_2)))])
