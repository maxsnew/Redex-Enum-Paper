#lang racket
(require redex
         "redex-model.rkt"
         (prefix-in : data/enumerate/lib)
         rackunit
         rackunit/log)

(provide
 (contract-out
  [from-nat+trace
   (-> e/unfair?
       exact-nonnegative-integer? 
       (values any/c
               (hash/c exact-nonnegative-integer?
                       (set/c exact-nonnegative-integer?))))])
 try-one
 get-trace
 complete-trace)

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

(define (complete-trace e n)
  (for/fold ([ht (make-hash)])
            ([i (in-range n)])
    (define this-one (get-trace e i))
    (for/hash ([(k v) (in-hash this-one)])
      (values k (set-union (hash-ref ht k (set)) v)))))

(define (n->nn n)
  (define level (integer-sqrt n))
  (define mid-level (/ (- (sqr (+ level 1)) (sqr level) 1) 2))
  (define distance (- n (sqr level)))
  (cond
    [(< distance mid-level)
     (cons distance level)]
    [else
     (cons level (- distance mid-level))]))

(define (:n->nn n)
  (:from-nat (:cons/e :natural/e :natural/e) n))

(module+ test
  (check-true
   (for/and ([x (in-range 1000)])
     (equal? (n->nn x) (:n->nn x)))))

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

(module+ test
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
  (check-equal? (term (ae-interp (* 2 ∞))) (term ∞))
  (check-equal? (term (ae-interp (* ∞ 2))) (term ∞))
  
  (check-equal? (term (size (below/e 2))) 2)
  (check-equal? (term (size (below/e ∞))) (term ∞))
  (check-equal? (term (size (cons/e (below/e ∞) (below/e 11)))) (term ∞))
  (check-equal? (term (size (cons/e (below/e 4) (below/e 11)))) 44)
  (check-equal? (term (size (unfair-cons/e (below/e ∞) (below/e 11)))) (term ∞))
  (check-equal? (term (size (unfair-cons/e (below/e 4) (below/e 11)))) 44)
  (check-equal? (term (size (or/e (below/e 4) (below/e 11)))) 15)
  (check-equal? (term (size (dep/e inf (below/e ∞) nat->map-of-swap-zero-with))) (term ∞))
  (check-equal? (term (size (dep/e fin (below/e 10) nat->below/e-of-that-nat)))
                450)
  (check-equal? (term (size (except/e (below/e 10) 3))) 9)
  (check-equal? (term (size (except/e (below/e ∞) 3))) (term ∞))
  (check-equal? (term (size (fix/e x (below/e ∞)))) (term ∞))
  
  
  (check-equal? 
   (:from-nat (term (to-enum (map/e swap-cons swap-cons (cons/e (below/e ∞) (below/e ∞)))))
              1)
   '(1 . 0))
  (check-equal? 
   (:from-nat (term (to-enum (cons/e (below/e ∞) (below/e ∞))))
              1)
   '(0 . 1))
  
  (check-equal? (term (sum-up-to (below/e ∞) nat->below/e-of-that-nat 10))
                (+ 0 1 2 3 4 5 6 7 8 9))
  
  ;; this property matches up to the way that sum-up-to-find-k is typeset
  (define (sum-up-to-find-k-prop n f e)
    (define ks (judgment-holds (sum-up-to-find-k ,n ,f ,e k) k))
    (cond
      [(= (length ks) 1)
       (define k (car ks))
       (and (<= (term (sum-up-to ,e ,f ,k)) n)
            (< n (term (sum-up-to ,e ,f ,(+ k 1)))))]
      [else #f]))
  
  (check-true (sum-up-to-find-k-prop 0
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  (check-true (sum-up-to-find-k-prop 1
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  (check-true (sum-up-to-find-k-prop 2
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  (check-true (sum-up-to-find-k-prop 10
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  (check-true (sum-up-to-find-k-prop 20
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  (check-true (sum-up-to-find-k-prop 50
                                     (term nat->below/e-of-that-nat)
                                     (term (below/e ∞))))
  
  
  (check-equal? (term (subst (cons/e (below/e ∞) (below/e ∞)) x (below/e ∞)))
                (term (cons/e (below/e ∞) (below/e ∞))))
  (check-equal? (term (subst (cons/e x x) x (below/e ∞)))
                (term (cons/e (below/e ∞) (below/e ∞))))
  (check-equal? (term (subst (cons/e x (fix/e x x)) x (below/e ∞)))
                (term (cons/e (below/e ∞) (fix/e x x))))
  (check-equal? (term (subst (cons/e x (fix/e y x)) x (below/e ∞)))
                (term (cons/e (below/e ∞) (fix/e y (below/e ∞)))))
  
  (check-equal? (judgment-holds (@<- (cons/e (below/e ∞) (below/e ∞)) n (cons 0 0) T) n)
                '(0))
  (check-equal? (judgment-holds (@<- (cons/e (below/e ∞) (below/e ∞)) n (cons 3 4) T) n)
                (list (:to-nat (:cons/e :natural/e :natural/e) (cons 3 4))))
  
  (try-many (term (below/e ∞)))
  (try-many (term (or/e (below/e ∞) (cons/e (below/e ∞) (below/e ∞)))))
  (try-many (term (or/e (cons/e (below/e ∞) (below/e ∞)) (below/e ∞))))
  (try-many (term (cons/e (below/e ∞) (below/e ∞))))
  (try-many (term (map/e (swap-zero-with 1) (swap-zero-with 1) (below/e ∞))))
  (try-many (term (map/e swap-cons swap-cons (cons/e (below/e ∞) (below/e ∞)))))
  (try-many (term (dep/e inf (below/e ∞) nat->map-of-swap-zero-with)))
  (try-many (term (dep/e fin (below/e 10000) nat->below/e-of-that-nat)))
  (try-many (term (except/e (below/e ∞) 1)))
  (try-many (term (fix/e bt (or/e (below/e ∞) (cons/e bt bt)))))
  (try-many (term (trace/e 0 (below/e ∞))))
  (try-many (term (cons/e (below/e 3) (below/e ∞))))
  (try-many (term (cons/e (below/e ∞) (below/e 3))))
  (try-many (term (cons/e (below/e 3) (below/e 5))))
  (try-many (term (cons/e (below/e 3) (below/e 2))))
  (try-many (term (or/e (cons/e (below/e 1) (below/e 100)) (below/e 10))))
  (try-many (term (or/e (below/e 10) (cons/e (below/e 1) (below/e 100)))))
  
  (check-equal? (:enum->list
                 (term (to-enum (map/e (swap-zero-with 3) (swap-zero-with 3) (below/e ∞))))
                 10)
                '(3 1 2 0 4 5 6 7 8 9))
  
  (check-equal? (get-trace (term (below/e ∞)) 0) (hash))
  (check-equal? (get-trace (term (trace/e 0 (below/e ∞))) 0) (hash 0 (set 0)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 (below/e ∞))
                                         (trace/e 1 (below/e ∞))))
                           0)
                (hash 1 (set 0) 0 (set 0)))
  (check-equal? (get-trace (term (or/e (trace/e 0 (below/e ∞))
                                       (trace/e 1 (cons/e (below/e ∞) (below/e ∞)))))
                           100)
                (hash 0 (set 50)))
  (check-equal? (get-trace (term (or/e (trace/e 0 (below/e ∞))
                                       (trace/e 1 (cons/e (below/e ∞) (below/e ∞)))))
                           101)
                (hash 1 (set 50)))
  (check-equal? (get-trace (term (cons/e (trace/e 0 (below/e ∞))
                                         (cons/e (trace/e 1 (below/e ∞))
                                                 (trace/e 2 (below/e ∞)))))
                           100)
                (hash 0 (set 0) 1 (set 1) 2 (set 3)))
  
  ;; test that the dep/e construction is actually not just
  ;; (cons/e (below/e ∞) (below/e ∞)) but that it shares a lot with it
  (define num-different 0)
  (define num-same 0)
  (for ([x (in-range 100)])
    (define l
      (judgment-holds 
       (@ (dep/e inf (below/e ∞) nat->map-of-swap-zero-with)
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
