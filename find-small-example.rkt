#lang racket/base
(require racket/runtime-path
         racket/place
         racket/match
         "util.rkt")
#|

This searches for a counterexample
ala the discussion in section 2

|#

(define-runtime-path find-small-example.rkt "find-small-example.rkt")
(module separate-place racket/base
  (require data/enumerate/lib
           racket/match
           racket/place
           "testing.scrbl")
  (provide start)
  (define (start chan)
    (define-values (e place-index place-count)
      (apply values (place-channel-get chan)))
    (follow-orders (case e
                     [(bt/e) bt/e]
                     [(un-bt/e) un-bt/e])
                   place-index place-count chan))
  
  (define (follow-orders e place-index place-count chan)
    (let loop ()
      (match (place-channel-get chan)
        [`(test ,start ,howmany)
         (define answer
           (let/ec k
             (for ([i (in-range start (+ start howmany))])
               (define t (from-nat e i))
               (when (and (not (bst? t)) (not-quite-bst? t))
                 (k `(answer ,i))))
             'nothing))
         (place-channel-put chan answer)
         (loop)]
        [`die (void)]))))

(define (spawn-places name place-count chunk-size)
  (define chans 
    (for/list ([place-index (in-range place-count)])
      (define pc (dynamic-place `(submod ,find-small-example.rkt separate-place) 'start))
      (place-channel-put pc (list name place-index place-count))
      pc))
  (let loop ([i 0])
    (for ([place-index (in-naturals)]
          [chan (in-list chans)])
      (define message `(test ,(+ i (* place-index chunk-size))
                             ,chunk-size))
      (place-channel-put chan message))
    (define answers
      (for/list ([chan (in-list chans)])
        (place-channel-get chan)))
    (define found-it
      (for/or ([answer (in-list answers)])
        (match answer
          [`(answer ,i) i]
          [`nothing #f])))
    (cond
      [found-it
       (for ([chan (in-list chans)])
         (place-channel-put chan 'die))
       (printf "counterexample index: ~a\n" found-it)]
      [else
       (define next-start (+ i (* place-count chunk-size)))
       (printf "tested ~a values ...\n" (add-commas next-start))
       (loop next-start)])))
      

(spawn-places 'bt/e 2 50)
(spawn-places 'un-bt/e 10 1000000)
