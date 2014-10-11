#lang racket

(require redex/benchmark/private/graph-data
         plot/pict pict
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
                 [plot-width 600] 
                 [plot-height 300]
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
  
  ;; (listof (list/c type data))
  (define types+datas
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
      (list type (reverse (cons (list max-t (/ (length pts) 2)) pts)))))
  
  (unless (= 3 (length types+datas)) 
    (error 'plot-lines.rkt "ack: assuming that there are only three competitors"))
  (define-values (_ crossover-points)
    (for/fold ([last-winner #f]
               [crossover-points '()])
      ([grammar-pr (in-list (list-ref (assoc 'grammar types+datas) 1))]
       [enum-pr (in-list (list-ref (assoc 'enum types+datas) 1))]
       [ordered-pr (in-list (list-ref (assoc 'ordered types+datas) 1))])
      (unless (and (= (list-ref grammar-pr 1)
                      (list-ref enum-pr 1))
                   (= (list-ref grammar-pr 1)
                      (list-ref ordered-pr 1)))
        (error 'plot-lines.rkt "ack: expected points to match up ~s ~s ~s"
               grammar-pr
               enum-pr
               ordered-pr))
      (define y-position (list-ref grammar-pr 1))
      (define grammar-time (list-ref grammar-pr 0))
      (define enum-time (list-ref enum-pr 0))
      (define ordered-time (list-ref ordered-pr 0))
      (define best (min grammar-time enum-time ordered-time))
      (define current-winner
        (cond
          [(= grammar-time best) 'grammar]
          [(= ordered-time best) 'ordered]
          [(= enum-time best) 'enum]))
      (values current-winner
              (cond
                [(and last-winner (not (equal? last-winner current-winner)))
                 (cons (point-label (vector best y-position)
                                    (format "~a, ~a"
                                            (number+unit/s y-position "bug")
                                            (format-time best))
                                    #:anchor 'bottom-right)
                       crossover-points)]
                [else
                 crossover-points]))))
  (append 
   crossover-points
   (for/list ([type+pts (in-list types+datas)]
              [n (in-naturals)])
     (define type (list-ref type+pts 0))
     (define pts (list-ref type+pts 1))
     (lines
      (reverse pts)
      ;#:width 2
      #:color (hash-ref type-colors type)
      #:style (list-ref line-styles n)
      #:label (hash-ref type-names type)))))

(define (format-time number)
  (cond
    [(<= number 60) (number+unit/s number "second")]
    [(<= number (* 60 60)) (number+unit/s (/ number 60) "minute")]
    [(<= number (* 60 60 24)) (number+unit/s (/ number 60 60) "hour")]
    [else (number+unit/s (/ number 60 60 24) "day")]))

(define (number+unit/s raw-n unit) 
  (define n (round raw-n))
  (format "~a ~a~a" n unit (if (= n 1) "" "s")))

(module+ test
  (require rackunit)
  (check-equal? (format-time 0) "0 seconds")
  (check-equal? (format-time 1) "1 second")
  (check-equal? (format-time 59) "59 seconds")
  (check-equal? (format-time 70) "1 minute")
  (check-equal? (format-time 110) "2 minutes")
  (check-equal? (format-time (* 60 60 2)) "2 hours")
  (check-equal? (format-time (* 60 60 #e2.2)) "2 hours")
  (check-equal? (format-time (* 60 60 #e8.2)) "8 hours")
  (check-equal? (format-time (* 60 60 24 3)) "3 days"))

(define (sort-stats stats)
  (for/fold ([h (hash)])
    ([s (in-list stats)])
    (hash-set h (second s)
              (cons (third s)
                    (hash-ref h (second s) '())))))

(define (correlation-plot filenames)
  (vl-append 10
             (single-correlation-plot filenames 'grammar 1)
             (single-correlation-plot filenames 'enum 2)
             (single-correlation-plot filenames 'ordered 3)))

(define (single-correlation-plot filenames type color)
  (define-values (d-stats b) (process-data (load-raw filenames)))
  (define type/index (hash 'S 0
                           'SM 1
                           'M 2
                           ;'MD 3
                           'D 3
                           'U 4))
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
                 [plot-x-label (hash-ref type-names type)]
                 [plot-y-label "Human Estimate of Bug Complexity"]
                 [plot-width 240]
                 [plot-height 240])
    (define unknowns (make-hash))
    (define unknown-x-position #e1e5)
    (define known-pts 
      (points 
       #:y-min -1
       #:y-max (hash-count type/index)
       #:x-max #e18e4
       #:sym (hash-ref type-symbols type)
       #:size (* (point-size) 1.5)
       #:color color
       (filter
        values
        (for/list ([base+num (in-list all-types/nums)])
          (define base (list-ref base+num 0))
          (define num (list-ref base+num 1))
          (define time (type+num+method->average
                        d-stats 
                        (cond
                          [(equal? base 'rvm)
                           'verification]
                          [else base])
                        num type))
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
    (plot-pict pts #:x-min 0.05 #:x-max #e18e4)))

(define/contract (type+num+method->average d-stats base num method)
  (-> any/c
      (or/c 'stlc 'poly-stlc 'stlc-sub 'let-poly 'list-machine 'rbtrees 'delim-cont 'verification) 
      any/c
      (or/c 'grammar 'ordered 'enum)
      (or/c #f (and/c real? positive?)))
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
