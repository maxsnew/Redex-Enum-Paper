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
      [(equal? num-points 0) '()]
      [else
       (define pr (index nat-pairs i))
       (hash-inc! arg1 (car pr))
       (hash-inc! arg2 (cdr pr))
       (cond
         [(equilibrium?)
          (cond
            [(number? num-points)
             (if (zero? num-points)
                 (list i)
                 (cons i (loop (+ i 1) (- num-points 1))))]
            [else
             (printf "~a\n" i)
             (loop (+ i 1) num-points)])]
         [else
          (loop (+ i 1) num-points)])])))

(define (unary-nat-equilibria-points)
  (for/list ([i (in-range num-points)])
    (/ (+ (* i i) (* i 3)) 2)))

(find-pair-equilibria nat-pairs 20)
(unary-nat-equilibria-points)

(find-pair-equilibria (⊗ binat-enum binat-enum) 10)
(for/list ([i (in-range 10)])
  (- (* (+ i 2) (expt 2 (- i 1))) 1))

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

  #;
  (λ (i) (index 
          (λ (p)
            (concatF
             (for/list ([k (in-range (+ p 1))])
               (⊗F (binat-enum k)
                   (binat-enum (- p k))))))
          i))
  
  #;
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

  #;
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

  #;
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

  #;
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

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(>= p 2)
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
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (let ([k 1])
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
                           (cons (f1 q) (f2 r)))))]
              [(>= p 3)
               ;; here we know the three cases in the definition of f1s
               ;; and the definition of f2s are all distinct
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
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               ;; here we know the three cases in the definition of f1s
               ;; and the definition of f2s are all distinct
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
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               ;; here we know the three cases in the definition of f1s
               ;; and the definition of f2s are all distinct
               (concatF
                (for/list ([k (in-range (+ p 1))])
                  (cond
                    [(zero? k)
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
                               (cons (f1 q) (f2 r))))]
                    [(= k 1)
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
                               (cons (f1 q) (f2 r))))]
                    [(= k (- p 1))
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
                               (cons (f1 q) (f2 r))))]
                    [(= k p)
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
                               (cons (f1 q) (f2 r))))]
                    [else
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
                               (cons (f1 q) (f2 r))))])))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               ;; here we know the three cases in the definition of f1s
               ;; and the definition of f2s are all distinct
               (concatF
                (for/list ([k (in-range (+ p 1))])
                  (cond
                    [(zero? k) (Finite 0 (λ (i) (error 'ack)))]
                    [(= k 1)
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
                               (cons (f1 q) (f2 r))))]
                    [(= k (- p 1))
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
                               (cons (f1 q) (f2 r))))]
                    [(= k p) (Finite 0 (λ (i) (error 'ack)))]
                    [else
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
                               (cons (f1 q) (f2 r))))])))]))
          i))
  
  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (concatF
                (for/list ([k (in-range 1 p)])
                  (cond
                    [(= k 1)
                     (define b (expt 2 (- p 3)))
                     (Finite b (λ (i) (cons 0 (+ b i))))]
                    [(= k (- p 1))
                     (define b (expt 2 (- k 2)))
                     (Finite b (λ (i) (cons (+ b i) 0)))]
                    [else
                     (define f1s (expt 2 (- k 2)))
                     (define f1 (λ (i) (+ (expt 2 (- k 2)) i)))
                     (define f2s (expt 2 (- (- p k) 2)))
                     (define f2 (λ (i) (+ (expt 2 (- (- p k) 2)) i)))
                     (Finite (* f1s f2s)
                             (λ (i)
                               (define-values (q r) (quotient/remainder i f2s))
                               (cons (f1 q) (f2 r))))])))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (concatF
                (for/list ([k (in-range 1 p)])
                  (cond
                    [(= k 1)
                     (define b (expt 2 (- p 3)))
                     (Finite b (λ (i) (cons 0 (+ b i))))]
                    [(= k (- p 1))
                     (define b (expt 2 (- p 3)))
                     (Finite b (λ (i) (cons (+ b i) 0)))]
                    [else
                     (define f1s (expt 2 (- k 2)))
                     (define f1 (λ (i) (+ (expt 2 (- k 2)) i)))
                     (define f2s (expt 2 (- (- p k) 2)))
                     (define f2 (λ (i) (+ (expt 2 (- (- p k) 2)) i)))
                     (Finite (* f1s f2s)
                             (λ (i)
                               (define-values (q r) (quotient/remainder i f2s))
                               (cons (f1 q) (f2 r))))])))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 (concatF
                  (for/list ([k (in-range 2 (- p 1))])
                    (define f1s (expt 2 (- k 2)))
                    (define f1 (λ (i) (+ (expt 2 (- k 2)) i)))
                    (define f2s (expt 2 (- (- p k) 2)))
                    (define f2 (λ (i) (+ (expt 2 (- (- p k) 2)) i)))
                    (Finite (* f1s f2s)
                            (λ (i)
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (f1 q) (f2 r))))))
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 (concatF
                  (for/list ([k2 (in-range 0 (- p 3))])
                    (define k (+ k2 2))
                    (define f1s (expt 2 (- k 2)))
                    (define f1 (λ (i) (+ (expt 2 (- k 2)) i)))
                    (define f2s (expt 2 (- (- p k) 2)))
                    (define f2 (λ (i) (+ (expt 2 (- (- p k) 2)) i)))
                    (Finite (* f1s f2s)
                            (λ (i)
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (f1 q) (f2 r))))))
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 (concatF
                  (for/list ([k (in-range 0 (- p 3))])
                    (define f1s (expt 2 k))
                    (define f1 (λ (i) (+ (expt 2 k) i)))
                    (define f2s (expt 2 (- p k 4)))
                    (define f2 (λ (i) (+ (expt 2 (- p k 4)) i)))
                    (Finite (* f1s f2s)
                            (λ (i)
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (f1 q) (f2 r))))))
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 (concatF
                  (for/list ([k (in-range 0 (- p 3))])
                    (define f1s (expt 2 k))
                    (define f1 (λ (i) (+ (expt 2 k) i)))
                    (define f2s (expt 2 (- p k 4)))
                    (define f2 (λ (i) (+ (expt 2 (- p k 4)) i)))
                    (Finite (expt 2 (- p 4))
                            (λ (i)
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (f1 q) (f2 r))))))
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle
                 (concatF
                  (for/list ([k (in-range 0 (- p 3))])
                    (define f1 (λ (i) (+ (expt 2 k) i)))
                    (define f2s (expt 2 (- p k 4)))
                    (define f2 (λ (i) (+ f2s i)))
                    (Finite (expt 2 (- p 4))
                            (λ (i)
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (f1 q) (f2 r)))))))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle
                 (for/fold ([tot-F emptyF]) ([k (in-range 0 (- p 3))])
                   (define f1 (λ (i) (+ (expt 2 k) i)))
                   (define f2s (expt 2 (- p k 4)))
                   (define f2 (λ (i) (+ f2s i)))
                   (⊕F tot-F
                       (Finite (expt 2 (- p 4))
                               (λ (i)
                                 (define-values (q r) (quotient/remainder i f2s))
                                 (cons (f1 q) (f2 r)))))))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle
                 (for/fold ([F1 emptyF]) ([k (in-range 0 (- p 3))])
                   (define f1 (λ (i) (+ (expt 2 k) i)))
                   (define f2s (expt 2 (- p k 4)))
                   (define f2 (λ (i) (+ f2s i)))
                   (define F2
                     (Finite (expt 2 (- p 4))
                             (λ (i)
                               (define-values (q r) (quotient/remainder i f2s))
                               (cons (f1 q) (f2 r)))))
                   (Finite (+ (Finite-size F1) (Finite-size F2))
                           (λ (n)
                             (if (< n (Finite-size F1))
                                 (!! F1 n)
                                 (!! F2 (- n (Finite-size F1))))))))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle
                 (for/fold ([F1 emptyF]) ([k (in-range 0 (- p 3))])
                   (define f1 (λ (i) (+ (expt 2 k) i)))
                   (define f2s (expt 2 (- p k 4)))
                   (define f2 (λ (i) (+ f2s i)))
                   (Finite (+ (Finite-size F1) (expt 2 (- p 4)))
                           (λ (n)
                             (if (< n (Finite-size F1))
                                 (!! F1 n)
                                 (let ([i (- n (Finite-size F1))])
                                   (define-values (q r) (quotient/remainder i f2s))
                                   (cons (f1 q) (f2 r))))))))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle
                 (for/fold ([F1 emptyF]) ([k (in-range 0 (- p 3))])
                   (define f1 (λ (i) (+ (expt 2 k) i)))
                   (define f2s (expt 2 (- p k 4)))
                   (define f2 (λ (i) (+ f2s i)))
                   (Finite (+ (Finite-size F1) (expt 2 (- p 4)))
                           (λ (n)
                             (if (< n (Finite-size F1))
                                 ((Finite-enc F1) n)
                                 (let ([i (- n (Finite-size F1))])
                                   (define-values (q r) (quotient/remainder i f2s))
                                   (cons (f1 q) (f2 r))))))))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define-values (middle-size middle-proc)
                 (for/fold ([F1-size 0] [F1-proc (λ (x) (error 'ack))])
                           ([k (in-range 0 (- p 3))])
                   (define f1 (λ (i) (+ (expt 2 k) i)))
                   (define f2s (expt 2 (- p k 4)))
                   (define f2 (λ (i) (+ f2s i)))
                   (values (+ F1-size (expt 2 (- p 4)))
                           (λ (n)
                             (if (< n F1-size)
                                 (F1-proc n)
                                 (let ([i (- n F1-size)])
                                   (define-values (q r) (quotient/remainder i f2s))
                                   (cons (f1 q) (f2 r))))))))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define-values (middle-size middle-proc)
                 (for/fold ([F1-size 0] [F1-proc (λ (x) (error 'ack))])
                           ([k (in-range 0 (- p 3))])
                   (define f2s (expt 2 (- p k 4)))
                   (values (+ F1-size (expt 2 (- p 4)))
                           (λ (n)
                             (if (< n F1-size)
                                 (F1-proc n)
                                 (let ([i (- n F1-size)])
                                   (define-values (q r) (quotient/remainder i f2s))
                                   (cons (+ (expt 2 k) q) (+ f2s r))))))))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define-values (_middle-size middle-proc)
                 (for/fold ([F1-size 0] [F1-proc (λ (x) (error 'ack))])
                           ([k (in-range 0 (- p 3))])
                   (define f2s (expt 2 (- p k 4)))
                   (values (+ F1-size (expt 2 (- p 4)))
                           (λ (n)
                             (if (< n F1-size)
                                 (F1-proc n)
                                 (let ([i (- n F1-size)])
                                   (define-values (q r) (quotient/remainder i f2s))
                                   (cons (+ (expt 2 k) q) (+ f2s r))))))))
               (define middle-size (* (- p 3) (expt 2 (- p 4))))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 1)
               (Finite 0 (λ (x) (error 'ack)))]
              [(= p 2)
               (Finite 1 (λ (i) (cons 0 0)))]
              [(>= p 3)
               (define middle-size (* (- p 3) (expt 2 (- p 4))))
               (define (middle-proc n)
                 (let loop ([F1-size (- middle-size (expt 2 (- p 4)))]
                            [k (- p 4)])
                   (define f2s (expt 2 (- p k 4)))
                   (if (< n F1-size)
                       (loop (- F1-size (expt 2 (- p 4)))
                             (- k 1))
                       (let ([i (- n F1-size)])
                         (define-values (q r) (quotient/remainder i f2s))
                         (cons (+ (expt 2 k) q) (+ f2s r))))))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 3)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (let loop ([F1-size (- middle-size twop4)]
                            [k (- p 2)])
                   (cond
                     [(< n F1-size)
                      (loop (- F1-size twop4)
                            (- k 1))]
                     [else
                      (define f2s (expt 2 (- p k 2)))
                      (define i (- n F1-size))
                      (define-values (q r) (quotient/remainder i f2s))
                      (cons (+ (expt 2 k) q) (+ f2s r))])))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 1)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  ;; this one tracks the value of iters
  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))

               (define (middle-proc n)
                 (let loop ([F1-size (- middle-size twop4)]
                            [k (- p 2)]
                            [iters 0])
                   (cond
                     [(< n F1-size)
                      (loop (- F1-size twop4)
                            (- k 1)
                            (+ iters 1))]
                     [else
                      (define iters2 (ceiling (/ (- middle-size twop4 n) twop4)))
                      (unless (if (zero? iters)
                                  (n . >= . (- middle-size twop4))
                                  (iters . = . (ceiling (/ (- middle-size twop4 n) twop4))))
                        (error 'ack))
                      (unless (= iters2 iters)
                        (error 'ack2))
                      (define f2s (expt 2 (- p k 2)))
                      (define i (- n F1-size))
                      (define-values (q r) (quotient/remainder i f2s))
                      (cons (+ (expt 2 k) q) (+ f2s r))])))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 1)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  #;
  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))

               (define (middle-proc n)
                 (let loop ([F1-size (- middle-size twop4)]
                            [k (- p 2)])
                   (cond
                     [(< n F1-size)
                      (loop (- F1-size twop4)
                            (- k 1))]
                     [else
                      (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                      (define F1-size (- (- middle-size twop4)
                                         (* iters twop4)))
                      (define final-k (- p 2 iters))
                      (define f2s (expt 2 (- p final-k 2)))
                      (define i (- n F1-size))
                      (define-values (q r) (quotient/remainder i f2s))
                      (cons (+ (expt 2 final-k) q) (+ f2s r))])))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 1)))
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (⊕F
                 middle
                 (Finite b (λ (i) (cons (+ b i) 0)))))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define middle (Finite middle-size middle-proc))
               (define b (expt 2 (- p 1)))

               (define (⊕F f1 f2)
                 (Finite (+ (Finite-size f1) (Finite-size f2))
                         (λ (n)
                           (if (< n (Finite-size f1))
                               (!! f1 n)
                               (!! f2 (- n (Finite-size f1)))))))
               
               (⊕F
                (Finite b (λ (i) (cons 0 (+ b i))))
                (let ([f1 middle]
                      [f2 (Finite b (λ (i) (cons (+ b i) 0)))])
                  (Finite (+ middle-size b)
                          (λ (n)
                            (if (< n middle-size)
                                (middle-proc n)
                                (cons (+ b (- n middle-size)) 0))))))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define b (expt 2 (- p 1)))

               (let ([f1 (Finite b (λ (i) (cons 0 (+ b i))))]
                     [f2 (Finite (+ middle-size b)
                                 (λ (n)
                                   (if (< n middle-size)
                                       (middle-proc n)
                                       (cons (+ b (- n middle-size)) 0))))])
                 (Finite (+ (Finite-size f1) (Finite-size f2))
                         (λ (n)
                           (if (< n (Finite-size f1))
                               (!! f1 n)
                               (!! f2 (- n (Finite-size f1)))))))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define b (expt 2 (- p 1)))

               (let ([f1 (Finite b (λ (i) (cons 0 (+ b i))))]
                     [f2 (Finite (+ middle-size b)
                                 (λ (n)
                                   (if (< n middle-size)
                                       (middle-proc n)
                                       (cons (+ b (- n middle-size)) 0))))])
                 (Finite (+ b middle-size b)
                         (λ (n)
                           (cond
                             [(< n (Finite-size f1))
                              (!! f1 n)]
                             [else
                              (!! f2 (- n (Finite-size f1)))]))))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define b (expt 2 (- p 1)))

               (let ([f2 (Finite (+ middle-size b)
                                 (λ (n)
                                   (if (< n middle-size)
                                       (middle-proc n)
                                       (cons (+ b (- n middle-size)) 0))))])
                 (Finite (+ b middle-size b)
                         (λ (n)
                           (cond
                             [(< n b)
                              (cons 0 (+ b n))]
                             [else
                              (!! f2 (- n b))]))))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define b (expt 2 (- p 1)))

               (Finite (+ b middle-size b)
                       (λ (n)
                         (cond
                           [(< n b)
                            (cons 0 (+ b n))]
                           [else
                            (if (< (- n b) middle-size)
                                (middle-proc (- n b))
                                (cons (+ b (- (- n b) middle-size)) 0))])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop4 (expt 2 (- p 2)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop4 n) twop4)))
                 (define F1-size (- (- middle-size twop4)
                                    (* iters twop4)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               (define b (expt 2 (- p 1)))

               (Finite (+ b middle-size b)
                       (λ (n)
                         (cond
                           [(< n b)
                            (cons 0 (+ b n))]
                           [(< (- n b) middle-size)
                            (middle-proc (- n b))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               (define (middle-proc n)
                 (define iters (ceiling (/ (- middle-size twop2 n) twop2)))
                 (define F1-size (- (- middle-size twop2)
                                    (* iters twop2)))
                 (define final-k (- p 2 iters))
                 (define f2s (expt 2 (- p final-k 2)))
                 (define i (- n F1-size))
                 (define-values (q r) (quotient/remainder i f2s))
                 (cons (+ (expt 2 final-k) q) (+ f2s r)))
               
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (middle-proc (- n twop1))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (let ([n (- n twop1)])
                              (define iters (ceiling (/ (- middle-size twop2 n) twop2)))
                              (define F1-size (- (- middle-size twop2)
                                                 (* iters twop2)))
                              (define final-k (- p 2 iters))
                              (define f2s (expt 2 (- p final-k 2)))
                              (define i (- n F1-size))
                              (define-values (q r) (quotient/remainder i f2s))
                              (cons (+ (expt 2 final-k) q) (+ f2s r)))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (define iters (ceiling (/ (- middle-size twop2 (- n twop1)) twop2)))
                            (define F1-size (- (- middle-size twop2) (* iters twop2)))
                            (define final-k (- p 2 iters))
                            (define f2s (expt 2 (- p final-k 2)))
                            (define i (- (- n twop1) F1-size))
                            (define-values (q r) (quotient/remainder i f2s))
                            (cons (+ (expt 2 final-k) q) (+ f2s r))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (define iters (ceiling (/ (- middle-size twop2 (- n twop1)) twop2)))
                            (define final-k (- p 2 iters))
                            (define f2s (expt 2 (- p final-k 2)))
                            (define i (- (- n twop1) (+ middle-size (- (* (+ iters 1) twop2)))))
                            (define-values (q r) (quotient/remainder i f2s))
                            (cons (+ (expt 2 final-k) q) (+ f2s r))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define middle-size (* (- p 1) (expt 2 (- p 2))))
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (define iters (ceiling (/ (- middle-size twop2 (- n twop1)) twop2)))
                            (define final-k (- p 2 iters))
                            (define f2s (expt 2 (- p final-k 2)))
                            (define i (+ n
                                         (- twop1)
                                         (- (+ middle-size (- (* (+ iters 1) twop2))))))
                            (define-values (q r) (quotient/remainder i f2s))
                            (cons (+ (expt 2 final-k) q) (+ f2s r))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))

  (λ (i) (index
          (λ (p)
            (cond
              [(= p 0)
               (Finite 1 (λ (i) (cons 0 0)))]
              [else
               (define twop2 (expt 2 (- p 2)))
               (define twop1 (expt 2 (- p 1)))
               (define middle-size (* (- p 1) twop2))
               (Finite (+ twop1 middle-size twop1)
                       (λ (n)
                         (cond
                           [(< n twop1)
                            (cons 0 (+ twop1 n))]
                           [(< (- n twop1) middle-size)
                            (define iters (ceiling (/ (- (* (- p 1) twop2) twop2 (- n twop1)) twop2)))
                            (define final-k (- p 2 iters))
                            (define f2s (expt 2 (- p final-k 2)))
                            (define i (+ n
                                         (- twop1)
                                         (- middle-size)
                                         (* (+ iters 1) twop2)))
                            (define-values (q r) (quotient/remainder i f2s))
                            (cons (+ (expt 2 final-k) q) (+ f2s r))]
                           [else
                            (cons (- n middle-size) 0)])))]))
          i))
  
  (λ (i)
    (define (get-card p)
      (cond
        [(= p 0) 1]
        [else
         (+ (expt 2 p)
            (* (- p 1) (expt 2 (- p 2))))]))
    (define (get-item p n)
      (cond
        [(= p 0)
         (cons 0 0)]
        [else
         (define twop1 (expt 2 (- p 1)))
         (define twop2 (expt 2 (- p 2)))
         (define middle-size (* (- p 1) twop2))
         (cond
           [(< n twop1)
            (cons 0 (+ twop1 n))]
           [(< n (+ twop1 middle-size))
            (define iters (ceiling (+ p (/ (- n) twop2))))
            (define f2s (expt 2 iters))
            (define i (+ n
                         (- twop1)
                         (* twop2 (+ iters 2 (- p)))))
            (define-values (q r) (quotient/remainder i f2s))
            (cons (+ (expt 2 (- p 2 iters)) q) (+ f2s r))]
           [else
            (cons (- n middle-size) 0)])]))
    (let go ([p 0] [i i])
      (cond
        [(< i (get-card p))
         (get-item p i)]
        [else (go (+ p 1)
                  (- i (get-card p)))])))
  
  

  ))
