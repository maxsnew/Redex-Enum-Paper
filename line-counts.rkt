#lang racket

(provide get-line-count)

(define type->base-files
  (hash 'stlc "stlc/stlc-base.rkt"
        'poly-stlc "poly-stlc/poly-stlc-base.rkt"
        'stlc-sub "stlc-sub/stlc-sub-base.rkt"
        'rbtrees "rbtrees/rbtrees-base.rkt"
        'list-machine "list-machine/list-machine-base.rkt"
        'delim-cont "delim-cont/delim-cont-base.rkt"))

(define (get-line-count type)
  (define path (collection-file-path (hash-ref type->base-files type) 
                                     "redex" "examples" "benchmark"))
  (number->string (line-count path)))

(define (line-count path)
  (call-with-input-file path
    (λ (in)
      (length
       (for/list ([line (in-lines in)]
                  #:unless (white-space/comment? line))
         'line)))))

(define (white-space/comment? line)
  (or (regexp-match? #rx"^[ \t]*$" line)
      (regexp-match? #rx"^;.*$" line)))