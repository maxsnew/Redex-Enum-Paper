#lang racket

(require redex/benchmark/private/graph-data
         plot/pict pict
         "process-data.rkt"
         racket/runtime-path)

(define-runtime-path all "all")

(provide plot-lines-from-directory
         type-name->description
         all
         order)

(module+ main
  (plot-lines-from-directory '("line-plot-enum.pdf" "line-plot-ordered.pdf")))

(define (plot-lines-from-directory [outputs #f])
  (define fst
    (plot-one-set-of-lines-from-directory
     (set 'grammar 'ordered 'ordered-mildly-unfair 'ordered-brutally-unfair)
     (and outputs (list-ref outputs 0))))
  (define snd
    (plot-one-set-of-lines-from-directory
     (set 'grammar 'enum 'enum-mildly-unfair 'enum-brutally-unfair)
     (and outputs (list-ref outputs 1))))
  (unless outputs
    (vc-append fst snd)))

(define (plot-one-set-of-lines-from-directory types-to-include output)
  (define directory all)
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory directory)))
  (parameterize ([plot-x-transform log-transform]
                 [plot-x-label "Time in Seconds"]
                 [plot-y-label "Number of Bugs Found"]
                 [plot-width 630] 
                 [plot-height 380]
                 [plot-x-ticks (log-ticks #:number 20 #:base 10)])
    (if output
        (plot-file (make-renderers data-stats types-to-include)
                   output
                   #:x-min 0.05)
        (plot-pict (make-renderers data-stats types-to-include)
                   #:x-min 0.05))))

(define (make-renderers stats types-to-include)
  (define max-t (apply max (map third stats)))
  
  ;; (listof (list/c type data))
  (define types+datas
    (sort
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
       (list type (reverse (cons (list max-t (/ (length pts) 2)) pts))))
     <
     #:key (λ (x) (hash-ref order (car x)))))

  ;; x-coordinate-map : hash[y -o> hash[type -o> x]]
  ;; maps each bug count total to a table of the time that
  ;; it took each attempt to find that many bugs
  (define bug-count-to-times-map (make-hash))
  (define max-bug-count 0)
  (for ([type+data (in-list types+datas)])
    (define type (list-ref type+data 0))
    (when (set-member? types-to-include type)
      (for ([point (in-list (list-ref type+data 1))])
        (define bug-count (list-ref point 1))
        (define time (list-ref point 0))
        (define ht (hash-ref! bug-count-to-times-map bug-count (λ () (make-hash))))
        (hash-set! ht type time)
        (set! max-bug-count (max bug-count max-bug-count)))))
  
  (define-values (_ crossover-points)
    (for/fold ([last-winner #f]
               [crossover-points '()])
              ([bug-count (in-range (+ max-bug-count 1))])
      (define y-table (hash-ref bug-count-to-times-map bug-count))
      (define-values (current-best-type current-best-time)
        (for/fold ([current-best-time #f]
                   [current-best-y #f])
                  ([(type time) (in-hash y-table)])
          (if (or (not current-best-time) (<= time current-best-y))
              (values type time)
              (values current-best-time current-best-y))))
      (values current-best-type
              (cond
                [(and last-winner (not (equal? last-winner current-best-type)))
                 (cons (point-label (vector current-best-time bug-count)
                                    (format "~a, ~a"
                                            (number+unit/s bug-count "bug")
                                            (format-time current-best-time))
                                    #:anchor 'bottom-right)
                       crossover-points)]
                [else
                 crossover-points]))))
  (append 
   crossover-points
   (for/list ([type+pts (in-list types+datas)]
              [n (in-naturals)]
              #:when (set-member? types-to-include (list-ref type+pts 0)))
     (define type (list-ref type+pts 0))
     (define pts (list-ref type+pts 1))
     (lines
      (reverse pts)
      #:color (hash-ref line-color type)
      #:width (hash-ref line-width type)
      #:style (hash-ref line-style type)
      #:label (type-name->description type)))))

(define line-width
  (hash 'grammar 3
        'ordered 1
        'ordered-mildly-unfair 1
        'ordered-brutally-unfair 1
        'enum 1
        'enum-mildly-unfair 1
        'enum-brutally-unfair 1))

(define line-style
  (hash 'grammar 'solid
        'ordered 'solid
        'ordered-mildly-unfair 'long-dash
        'ordered-brutally-unfair 'dot
        'enum 'solid
        'enum-mildly-unfair 'long-dash
        'enum-brutally-unfair 'dot))

(define line-color
  (hash 'grammar 0
        'ordered 1
        'ordered-mildly-unfair 1
        'ordered-brutally-unfair 1
        'enum 2
        'enum-mildly-unfair 2
        'enum-brutally-unfair 2))

(define order (hash 'grammar 0
                    'ordered 1
                    'ordered-mildly-unfair 2
                    'ordered-brutally-unfair 3
                    'enum 4
                    'enum-mildly-unfair 5
                    'enum-brutally-unfair 6))
  
(define (type-name->description name)
  (case name
    [(grammar) "Ad Hoc Random Generation"]
    [(ordered) "In-Order Enumeration, Fair"]
    [(ordered-mildly-unfair) "In-Order Enumeration, Mildly Unfair"]
    [(ordered-brutally-unfair) "In-Order Enumeration, Brutally Unfair"]
    [(enum) "Uniform Random Selection, Fair"]
    [(enum-mildly-unfair) "Uniform Random Selection, Mildly Unfair"]
    [(enum-brutally-unfair) "Uniform Random Selection, Brutally Unfair"]))

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
