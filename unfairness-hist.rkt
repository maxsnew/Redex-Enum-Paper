#lang racket
(require redex/private/enumerator
         pict
         plot)

(provide unfairness-histograms)
(define total-size 1000)

(define unfair (cons/e nat/e (cons/e nat/e nat/e)))
(define fair (list/e nat/e nat/e nat/e))

(define (unfairness-histograms)
  (define unfair-hashes (build-hashes unfair))
  (define fair-hashes (build-hashes fair))
  (define-values (max-x max-y) (find-maxes unfair-hashes fair-hashes))
  (vc-append 
   (build-plots fair-hashes max-x max-y #f #t)
   (build-plots unfair-hashes max-x max-y #t #f)))

(define (find-maxes v1 v2)
  (define max-x 0)
  (define max-y 0)
  (for ([v (in-list (list v1 v2))])
    (for ([h (in-vector v)])
      (for ([(k v) (in-hash h)])
        (set! max-x (max k max-x))
        (set! max-y (max v max-y)))))
  (values max-x max-y))

(define (build-hashes enumerator)
  (define hashes (vector (make-hash) (make-hash) (make-hash)))
  (for ([x (in-range total-size)])
    (for/list ([x (in-list (flatten (decode enumerator x)))]
               [i (in-naturals)])
      (define ht (vector-ref hashes i))
      (hash-set! ht x (+ 1 (hash-ref ht x 0)))))
  hashes)

(define (build-plots hashes max-x max-y x-labels? fair?)
  (apply hc-append
         4
         (text (format "Occurrences w/ ~a"
                       (if fair? "Fair" "Unfair"))
               'roman
               10
               (* pi 1/2))
         (for/list ([x (in-vector hashes)]
                    [i (in-naturals)])
           (plot-one x max-x max-y
                     (and x-labels?
                          (format "Value in ~a component"
                                  (case i
                                    [(0) "first"]
                                    [(1) "second"]
                                    [(2) "third"]
                                    [else (error 'ack-unfairness)])))
                     #f))))

(define (plot-one hash max-x max-y x-label y-label)
  (parameterize ([plot-y-far-ticks no-ticks]
                 [plot-x-ticks (linear-ticks)])
    (plot-pict
     #:x-max max-x
     #:y-max max-y
     #:x-label x-label
     #:y-label y-label
     (list
      (parameterize ([plot-font-size 6])
        (x-ticks (for/list ([x (in-range (+ max-x 1))]
                            #:when (zero? (modulo x 4)))
                   (tick (+ x .5) #t (format "~a" x)))))
      (discrete-histogram
       #:add-ticks? #f
       (sort
        (for/list ([(k v) (in-hash hash)])
          (vector k v))
        < 
        #:key (λ (x) (vector-ref x 0))))))))

(module+ main 
  (require slideshow)
  (slide
   (scale-to-fit
    (unfairness-histograms)
    client-w client-h)))
