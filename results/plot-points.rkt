#lang racket/base

(provide plot-points-from-directory)
(require racket/class
         racket/draw
         pict
         redex/benchmark/private/graph-data
         "process-data.rkt"
         "plot-lines.rkt"
         plot
         racket/math)

(define (plot-points-from-directory [output #f])
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory all)))
  
  (parameterize ([type-names type-name->description]
                 [plot-width 450]
                 [plot-x-label #f]
                 [type-symbols (λ (x)
                                 (case x
                                   [(grammar) 'triangle]
                                   [(ordered) '5star]
                                   [(enum) 'circle]
                                   [(ordered-brutally-unfair) 'otimes]
                                   [(enum-mildly-unfair) 'odot]
                                   [(ordered-mildly-unfair) 'oasterisk]
                                   [(enum-brutally-unfair) 'full7star]))]
                 [plot-y-label "Average Number of Seconds to Find Bug"])
    (define pict
      (make-plot/data-stats/name-avgs data-stats name-avgs all-names
                                      max-non-f-value-from-list-ref-d2
                                      #t))
    (cond
      [output
       (define dc (new pdf-dc% [output output] [interactive #f]))
       (send dc start-doc "")
       (send dc start-page)
       (draw-pict pict dc 0 0)
       (send dc end-page)
       (send dc end-doc)]
      [else pict])))

(module+ main
  (plot-points-from-directory "points-plot.pdf"))