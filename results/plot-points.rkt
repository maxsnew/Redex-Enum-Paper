#lang racket/base

(provide plot-points-from-directory)
(require redex/benchmark/private/graph-data
         "process-data.rkt"
         "plot-lines.rkt"
         plot
         racket/math)

(define (plot-points-from-directory directory)
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory directory)))
  
  (parameterize ([type-names type-name->description]
                 [plot-width 450]
                 [plot-x-label #f]
                 [plot-y-label "Average Number of Seconds to Find Bug"])
    (make-plot/data-stats/name-avgs data-stats name-avgs all-names
                                    max-non-f-value-from-list-ref-d2
                                    #t)))
