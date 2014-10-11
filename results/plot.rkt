#lang racket

(require "plot-lines.rkt"
         redex/benchmark/private/graph-data
         racket/runtime-path
         plot/pict
         pict)

(provide (all-defined-out))

(define-runtime-path 4-hour "4-hour")
(define-runtime-path 24-hour "24-hour")

(define (res-plot-4hour)
  (plot-results
   (dir->files 4-hour)))

(define (dir->files d)
  (for/list ([f (in-directory d)]) 
    (path->string (path->complete-path f d))))

(define (res-plot-24hour)
  (plot-results
   (dir->files 24-hour)))

(define (plot-results fnames)
  (parameterize ([confidence-interval #t]
                 ;[order-by 'grammar]
                 [types '(grammar enum ordered)]
                 [plot-width 650]
                 [plot-height 400])
    (make-plot fnames)))

(define (line-plot-4hour)
  (plot-from-files (dir->files 4-hour)))

(define (line-plot-24hour)
  (plot-from-files (dir->files 24-hour)))

(define (correlation-plot-4hour)
  (correlation-plot (dir->files 4-hour)))

(define (correlation-plot-24hour)
  (correlation-plot (dir->files 24-hour)))

(define (unique-sucesses-24hour)
  (unique-sucesses (dir->files 24-hour)))
