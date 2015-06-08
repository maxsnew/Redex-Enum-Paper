#lang racket

(define/contract (fllog n)
  (-> exact-positive-integer? exact-nonnegative-integer?)
  (let loop ([n n])
    (cond
      [(= n 1) 0]
      [else (+ 1 (loop (quotient n 2)))])))

(define (count-up n)
  (let loop ([n n]
             [group-size 3])
  (cond
    [(<= n 0) 0]
    [else
     (+ (loop (- n group-size)
              (- (* (+ group-size 1) 2) 1))
        1)])))

(define (bad-n+n->n left? n)
  (if left?
      (if (zero? n)
          0
          (expt 2 (- n 1)))
      (+ n (count-up n) 3)))

(define (bad-n->n+n n)
  (cond
    [(zero? n) (values #t 0)]
    [else
     (define f (fllog n))
     (cond
       [(= (expt 2 f) n)
        (values #t (+ f 1))]
       [else
        (values #f (- n (fllog n) 2))])]))

(module+ main
  (time
   (for ([i (in-range 100000)])
     (define-values (left? n) (bad-n->n+n i))
     (define j (bad-n+n->n left? n))
     (unless (= i j)
       (eprintf "bad-bijection-fails: ~s => ~s ~s => ~s\n"
                i left? n j)))))
