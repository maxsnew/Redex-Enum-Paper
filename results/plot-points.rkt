#lang racket

(provide plot-points-from-directory)
(require racket/draw
         pict
         plot
         redex/benchmark/private/graph-data
         "process-data.rkt"
         "plot-lines.rkt")

(define type-syms
  (hash 'grammar 'triangle
        'ordered 'asterisk
        'ordered-mildly-unfair 'otimes
        'ordered-brutally-unfair 'oasterisk
        'enum 'plus
        'enum-mildly-unfair 'circle
        'enum-brutally-unfair 'oplus))
        
(define (plot-points-from-directory [output #f])
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory all)))

  (set! data-stats (sort data-stats <
                         #:key (λ (x) (hash-ref order (list-ref x 1)))))
                         
  
  (parameterize ([type-names type-name->description]
                 [plot-width 600]
                 [plot-height 500]
                 [plot-x-label #f]
                 [type-symbols (λ (x) (hash-ref type-syms x))]
                 [plot-y-label "Average Number of Seconds to Find Bug"])
    (define pict
      (make-plot/data-stats/name-avgs data-stats name-avgs all-names
                                      max-non-f-value-from-list-ref-d2
                                      #t))
    (cond
      [output
       (define dc (new pdf-dc% [output output] [interactive #f] [use-paper-bbox #f] [as-eps #t]))
       (send dc start-doc "")
       (send dc start-page)
       (draw-pict pict dc 0 0)
       (send dc end-page)
       (send dc end-doc)]
      [else pict])))

(module+ main
  (plot-points-from-directory "points-plot.pdf"))