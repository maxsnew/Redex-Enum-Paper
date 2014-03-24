#lang racket

(require redex/examples/benchmark/graph-data
         plot
         "graph-data.rkt"
         "../bug-info.rkt")

(provide plot-from-files
         correlation-plot
         unique-sucesses)

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
  (define type/index (hash 'S 0
                           'SM 1
                           'M 2
                           'MD 3
                           'D 4
                           'U 5))
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
    (define unknown-x-position #e1e5)
    (define known-pts 
      (points 
       #:y-min -1
       #:y-max (hash-count type/index)
       #:x-max #e16e4
       (filter
        values
        (for/list ([base+num (in-list all-types/nums)])
          (define base (list-ref base+num 0))
          (define num (list-ref base+num 1))
          (define time (type+num+method->average d-stats base num 'grammar))
          (define cat (hash-ref (hash-ref type->num->cat base) num))
          ;; no time => no success; collect them to put on the rhs
          (unless time 
            (hash-set! unknowns cat (+ 1 (hash-ref unknowns cat 0))))
          (define (fail)
            (error 'plot-lines.rkt "unknown category ~s ~s" cat base+num))
          (and time
               (list time
                     (hash-ref type/index 
                               cat 
                               fail)))))))
    (define unknown-pts
      (for/list ([(cat count) (in-hash unknowns)])
        (point-label (list unknown-x-position (hash-ref type/index cat))
                     (format "~a" count)
                     #:anchor 'right)))
    (define pts (cons known-pts unknown-pts))
    (if output
        (plot-file pts output #:x-min 0.05)
        (plot-pict pts #:x-min 0.05))))


(define/contract (type+num+method->average d-stats base num method)
  (-> any/c any/c any/c (or/c 'grammar 'ordered 'enum) (or/c #f (and/c real? positive?)))
  (define fn (format "~a-~a.rkt" base num))
  (for/or ([ele (in-list d-stats)])
    (define filename (list-ref ele 0))
    (define-values (base name dir) (split-path filename))
    (and (equal? (path->string name) fn)
         (equal? method (list-ref ele 1))
         (list-ref ele 2))))

(define/contract (unique-sucesses filenames)
  (-> (listof any/c)
      (hash/c (or/c 'grammar 'ordered 'enum)
              (listof (list/c symbol? number?))))
  
  ;; success-table : hash[(list/c base num) -o> (setof method)])
  (define success-table (make-hash))
  
  (define-values (d-stats b) (process-data (load-raw filenames)))
  (for ([base+num (in-list all-types/nums)])
    (define base (list-ref base+num 0))
    (define num (list-ref base+num 1))
    (for ([method (in-list '(grammar ordered enum))])
      (when (type+num+method->average d-stats base num method)
        (define key (list base num))
        (hash-set! success-table key
                   (set-add (hash-ref success-table key (set))
                            method)))))
  
  (define inverted-table (make-hash '((grammar . ()) (ordered . ()) (enum . ()))))
  (for ([(k v) (in-hash success-table)])
    (when (= (set-count v) 1)
      (define method (car (set->list v)))
      (hash-set! inverted-table method (cons k (hash-ref inverted-table method '())))))
  (for/hash ([(k v) (in-hash inverted-table)])
    (values k (sort v string<=? #:key (λ (x) (format "~s" x))))))
