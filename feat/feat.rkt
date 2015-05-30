#lang racket
(require data/enumerate racket/promise)
(module+ test (require rackunit))

(struct Finite (size enc))
(define emptyF (Finite 0 (λ (p) (error 'emptyF))))
(define (singletonF a) (Finite 1 (λ (p) (if (zero? p) a (error "out of bounds")))))
(define (card f) (Finite-size f))
(define (!! f n) ((Finite-enc f) n))
(module+ test (check-equal? (!! (singletonF 'x) 0) 'x))
    
(define (⊕F f1 f2)
  (Finite (+ (Finite-size f1) (Finite-size f2))
          (λ (n)
            (if (< n (Finite-size f1))
                (!! f1 n)
                (!! f2 (- n (Finite-size f1)))))))
(module+ test
  (define x-and-y (⊕F (singletonF 'x) (singletonF 'y)))
  (check-equal? (!! x-and-y 0) 'x)
  (check-equal? (!! x-and-y 1) 'y))


(define (⊗F f1 f2)
  (Finite (* (Finite-size f1) (Finite-size f2))
          (λ (i)
            (define-values (q r) (quotient/remainder i (card f2)))
            (cons (!! f1 q) (!! f2 r)))))
(module+ test
  (check-equal? (!! (⊗F (singletonF 'x) (singletonF 'y)) 0)
                (cons 'x 'y))
  (check-equal? (for/set ([i (in-range 4)])
                  (!! (⊗F x-and-y x-and-y) i))
                (set (cons 'x 'x) (cons 'x 'y) (cons 'y 'x) (cons 'y 'y))))

(define (valuesF F)
  (for/list ([i (in-range (Finite-size F))])
    ((Finite-enc F) i)))

(define (concatF Fs)
  (for/fold ([tot-F emptyF]) ([F (in-list Fs)])
    (⊕F tot-F F)))
(define (bimapF f F) (Finite (Finite-size F) (λ (x) (f ((Finite-enc F) x)))))

(module+ test
  (check-equal? (!! (bimapF add1 (singletonF 0)) 0) 1)
  (check-equal? (for/list ([i (in-range 3)])
                  (!! (concatF (list (singletonF 'x)
                                     (singletonF 'y)
                                     (singletonF 'z)))
                      i))
                '(x y z)))

(define (index e i)
  (let go ([p 0] [i i])
    (cond
      [(< i (card (e p)))
       (!! (e p) i)]
      [else (go (+ p 1)
                (- i (card (e p))))])))


(define (singleton a) (λ (n) (if (zero? n) (singletonF a) emptyF)))
(define ((⊕ e1 e2) p) (⊕F (e1 p) (e2 p)))
(define ((⊗ e1 e2) p)
  (concatF
   (for/list ([k (in-range (+ p 1))])
     (⊗F (e1 k) (e2 (- p k))))))
(module+ test
  (check-equal? (index (⊗ (singleton 'x) (singleton 'y)) 0)
                '(x . y)))

(define ((pay e) n)
  (cond
    [(zero? n) emptyF]
    [else (e (- n 1))]))

(define ((bimap f e) n) (bimapF f (e n)))
(define-syntax-rule (del e) (let ([p (delay e)]) (λ (n) ((force p) n))))

(define unat-enum (del (pay (⊕ (singleton 0) (bimap add1 unat-enum)))))
(define (binat-enum p)
  (Finite (cond
            [(zero? p) 0]
            [(= p 1) 1]
            [else (expt 2 (- p 2))])
          (if (= p 1)
              (λ (i) 0)
              (λ (i) (+ (expt 2 (- p 2)) i)))))

(define nat-pairs (⊗ unat-enum unat-enum))

(define num-points 20)

(define (find-pair-equilibria nat-pairs [num-points num-points])
  (define arg1 (make-hash))
  (define arg2 (make-hash))
  (define (equilibrium?) (and (subset? arg1 arg2) (subset? arg2 arg1)))
  (define (subset? ht1 ht2)
    (for/and ([(k v) (in-hash ht1)])
      (equal? (hash-ref ht2 k #f) v)))
  (define (hash-inc! ht k) (hash-set! ht k (+ (hash-ref ht k 0) 1)))
  (let loop ([i 0]
             [num-points num-points])
    (cond
      [(zero? num-points) '()]
      [else
       (define pr (index nat-pairs i))
       (hash-inc! arg1 (car pr))
       (hash-inc! arg2 (cdr pr))
       (cond
         [(equilibrium?)
          (if (zero? num-points)
              (list i)
              (cons i (loop (+ i 1) (- num-points 1))))]
         [else
          (loop (+ i 1) num-points)])])))

(define (unary-nat-equilibria-points)
  (for/list ([i (in-range num-points)])
    (/ (* i (+ i 3)) 2)))

;(find-pair-equilibria nat-pairs)
;(unary-nat-equilibria-points)

;(find-pair-equilibria (⊗ binat-enum binat-enum) 7)

(define (check-same . enums)
  (for ([enum1 (in-list enums)]
        [enum2 (in-list (cdr enums))]
        [enum-i (in-naturals 1)])
    (for ([i (in-range 1000)])
      (unless (equal? (enum1 i) (enum2 i))
        (error 'check-same "enum ~a and ~a are different at position ~a: ~s vs ~s"
               enum-i (+ enum-i 1)
               i
               (enum1 i)
               (enum2 i))))))

(time
 (check-same
  (λ (i) (index (⊗ binat-enum binat-enum) i))

  (λ (i) (index 
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (⊗F (binat-enum k)
                   (binat-enum (- p k))))))
          i))
  
  (λ (i) (index
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (define f1 (binat-enum k))
               (define f2 (binat-enum (- p k)))
               (Finite (* (Finite-size f1) (Finite-size f2))
                       (λ (i)
                         (define-values (q r) (quotient/remainder i (card f2)))
                         (cons (!! f1 q) (!! f2 r)))))))
          i))

  (λ (i) (index
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (define f1
                 (Finite (cond
                           [(zero? k) 0]
                           [(= k 1) 1]
                           [else (expt 2 (- k 2))])
                         (if (= k 1)
                             (λ (i) 0)
                             (λ (i) (+ (expt 2 (- k 2)) i)))))
               (define f2
                 (Finite (cond
                           [(zero? (- p k)) 0]
                           [(= (- p k) 1) 1]
                           [else (expt 2 (- (- p k) 2))])
                         (if (= (- p k) 1)
                             (λ (i) 0)
                             (λ (i) (+ (expt 2 (- (- p k) 2)) i)))))
               (Finite (* (Finite-size f1) (Finite-size f2))
                       (λ (i)
                         (define-values (q r) (quotient/remainder i (card f2)))
                         (cons (!! f1 q) (!! f2 r)))))))
          i))

  (λ (i) (index
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (define f1s (cond
                             [(zero? k) 0]
                             [(= k 1) 1]
                             [else (expt 2 (- k 2))]))
               (define f1 (if (= k 1)
                              (λ (i) 0)
                              (λ (i) (+ (expt 2 (- k 2)) i))))
               (define f2s (cond
                             [(zero? (- p k)) 0]
                             [(= (- p k) 1) 1]
                             [else (expt 2 (- (- p k) 2))]))
               (define f2
                 (if (= (- p k) 1)
                     (λ (i) 0)
                     (λ (i) (+ (expt 2 (- (- p k) 2)) i))))
               (Finite (* f1s f2s)
                       (λ (i)
                         (define-values (q r) (quotient/remainder i f2s))
                         (cons (f1 q) (f2 r)))))))
          i))

  (λ (i) (index
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (define f1s (cond
                             [(zero? k) 0]
                             [(= k 1) 1]
                             [else (expt 2 (- k 2))]))
               (define f1 (if (= k 1)
                              (λ (i) 0)
                              (λ (i) (+ (expt 2 (- k 2)) i))))
               (define f2s (cond
                             [(= k p) 0]
                             [(= k (- p 1)) 1]
                             [else (expt 2 (- (- p k) 2))]))
               (define f2
                 (if (= k (- p 1))
                     (λ (i) 0)
                     (λ (i) (+ (expt 2 (- (- p k) 2)) i))))
               (Finite (* f1s f2s)
                       (λ (i)
                         (define-values (q r) (quotient/remainder i f2s))
                         (cons (f1 q) (f2 r)))))))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [else
               (concatF
                (for/list ([k (in-range (+ p 1))])
                  (define f1s (cond
                                [(zero? k) 0]
                                [(= k 1) 1]
                                [else (expt 2 (- k 2))]))
                  (define f1 (if (= k 1)
                                 (λ (i) 0)
                                 (λ (i) (+ (expt 2 (- k 2)) i))))
                  (define f2s (cond
                                [(= k p) 0]
                                [(= k (- p 1)) 1]
                                [else (expt 2 (- (- p k) 2))]))
                  (define f2
                    (if (= k (- p 1))
                        (λ (i) 0)
                        (λ (i) (+ (expt 2 (- (- p k) 2)) i))))
                  (Finite (* f1s f2s)
                          (λ (i)
                            (define-values (q r) (quotient/remainder i f2s))
                            (cons (f1 q) (f2 r))))))]))
          i))))
