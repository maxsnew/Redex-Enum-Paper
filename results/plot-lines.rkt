#lang racket

(require redex/examples/benchmark/graph-data
         plot
         "graph-data.rkt"
         "../bug-info.rkt")

(provide plot-from-files
         correlation-plot)

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
                 [plot-x-label "Time in Seconds"]
                 [plot-y-label "Number of Bugs Found"]
                 [plot-width 800] 
                 [plot-height 400]
                 [plot-x-ticks (log-ticks #:number 20 #:base 10)])
    (if output
        (plot-file (make-renderers d-stats)
                   output
                   #:x-min 0.05)
        (plot-pict (make-renderers d-stats)
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


(define (correlation-plot filenames [output #f])
  (define-values (d-stats b) (process-data (load-raw filenames)))
  (define (base+num+method->average base num method)
    (define fn (format "~a-~a.rkt" base num))
    (for/or ([ele (in-list d-stats)])
      (define filename (list-ref ele 0))
      (define-values (base name dir) (split-path filename))
      (and (equal? (path->string name) fn)
           (equal? method (list-ref ele 1))
           (list-ref ele 2))))
  (define type/index (hash 'S 0
                           'SM 1
                           'M 2
                           'MD 3
                           'D 4
                           'SD 5
                           'SMD 6
                           '? 7))
  (define index/type (for/hash ([(k v) (in-hash type/index)])
                       (values v k)))

  (define the-y-ticks
    (ticks 
     (λ (r1 r2) 
       (for/list ([i (in-range (hash-count type/index))])
         (pre-tick i #t)))
     (λ (r1 r2 pre-ticks)
       (for/list ([n (in-range (hash-count type/index))])
         (format "~a" (hash-ref index/type n))))))
  
  (parameterize ([plot-x-transform log-transform]
                 [plot-y-ticks the-y-ticks]
                 [plot-x-ticks (log-ticks #:number 20 #:base 10)]
                 [plot-x-label "Time in Seconds"]
                 [plot-y-label "Human Estimate of Bug Complexity"]
                 [plot-width 270]
                 [plot-height 270])
    (define unknowns (make-hash))
    (define unknown-x-position #e1e4)
    (define known-pts 
      (points 
       #:y-min -1
       #:y-max (hash-count type/index)
       #:x-max #e16e3
       (filter
        values
        (for/list ([base+num (in-list all-types/nums)])
          (define base (list-ref base+num 0))
          (define num (list-ref base+num 1))
          (define time (base+num+method->average base num 'grammar))
          (define cat (hash-ref (hash-ref type->num->cat base) num))
          ;; no time => no success; collect them to put on the rhs
          (unless time 
            (hash-set! unknowns cat (+ 1 (hash-ref unknowns cat 0))))
          (and time
               (list time
                     (hash-ref type/index cat)))))))
    (define unknown-pts
      (for/list ([(cat count) (in-hash unknowns)])
        (point-label (list unknown-x-position (hash-ref type/index cat))
                     (format "~a" count)
                     #:anchor 'right)))
    (define pts (cons known-pts unknown-pts))
    (if output
        (plot-file pts output)
        (plot-pict pts))))
