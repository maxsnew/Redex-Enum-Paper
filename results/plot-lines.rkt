#lang racket

(require "graph-data.rkt"
         plot)

(provide plot-from-files)

(module+
    main
  (require racket/cmdline)
  (command-line
   #:args filenames
   (plot-from-files filenames "line-plot.pdf")))

(define (plot-from-files filenames [output #f])
  (define-values (d-stats _)
    (process-data
     (load-raw filenames)))
  (parameterize ([plot-x-transform log-transform]
                 [plot-x-ticks (log-ticks #:number 20 #:base 10)])
    (if output
        (plot-file (make-renderers d-stats)
                   output
                   #:y-label "# bugs found"
                   #:x-label "seconds"
                   #:x-min 0.05)
        (plot-pict (make-renderers d-stats)
                   #:y-label "# bugs found"
                   #:x-label "seconds"
                   #:x-min 0.05))))

(define line-styles
  (list 'solid 'dot 'long-dash
        'short-dash 'dot-dash))

(define (make-renderers stats)
  (define max-t (apply max (map third stats)))
  (for/list ([(type avgs) (in-hash (sort-stats stats))]
             [n (in-naturals)])
    (define pts 
      (for/fold ([l '()]) 
        ([a (sort avgs <)]
         [c (in-naturals)])
        (cons (list a (add1 c))
              (cons 
               (list a c) 
               l))))
    (lines
     (reverse (cons (list max-t (/ (length pts) 2)) pts))
     ;#:width 2
     #:color (hash-ref type-colors type)
     #:style (list-ref line-styles n)
     #:label (hash-ref type-names type))))

(define (sort-stats stats)
  (for/fold ([h (hash)])
    ([s (in-list stats)])
    (hash-set h (second s)
              (cons (third s)
                    (hash-ref h (second s) '())))))