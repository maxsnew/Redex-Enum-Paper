#lang racket

(require plot redex/private/enumerator)

(define ns (for/list ([i (in-range 7)])
             nat/e))
(define l/e
  (apply list/e ns))

(define (avgs n)
  (define-values
    (_ lst)
    (for/fold ([prev (for/list ([x (in-list ns)]) 0)]
             [lst  '()])
            ([i (in-range n)])
    (define cur (decode l/e (add1 i)))
    (define sum (map + prev cur))
    (values sum (cons (map (λ (x) (/ x (+ 1.0 i))) sum) lst))))
  (reverse lst))

(define avs (avgs 100000))
(define (with-indices xs f)
  (lines
  (for/list ([i (in-naturals)]
             [x (in-list xs)])
    (vector i
            (f x)))))
(plot
 (for/list ([i (in-naturals)]
            [_ (in-list ns)])
   (with-indices avs (λ (l) (list-ref l i)))))