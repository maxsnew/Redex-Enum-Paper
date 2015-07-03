#lang racket
(require data/enumerate/lib
         pict
         redex/pict
         scribble/manual
         rackunit)

(provide pair-pict cantor-cons-pict
         disj-sum-pict/good disj-sum-pict/bad
         grid gen-grid
         unfair-exp fair-exp num-enumerated
         max-unfair min-unfair max-fair min-fair
         render-enumerations
         enum-example
         except/e*
         fin/e
         lon/e-code lon/e
         lon2/e-code lon2/e)

(define (disj-sum-pict/good)
  (gen-table or/e 8 24 40 8 #:arrows? #t))

(define (disj-sum-pict/bad)
  (define (bad-disj-sum/e a b c)
    (or/e a (or/e b c)))
  (gen-table bad-disj-sum/e 8 32 40 8 #:arrows? #t #:last-arrow 15))

(define (gen-table or/e y-count num-points size-per-cell arrow-head-size
                   #:arrows? arrows? #:last-arrow [last-arrow +inf.0])
  (define x-count 3)
  (define width (* size-per-cell x-count))
  (define height (* size-per-cell y-count))
  (define prs (or/e natural/e char/e flonum/e))
  (define base
    (dc (λ (dc dx dy)
          #;
          (for ([i (in-range 1 x-count)])
            (send dc draw-line 
                  (+ dx (* i size-per-cell))
                  dy
                  (+ dx (* i size-per-cell))
                  (+ dy height)))
          #;
          (for ([i (in-range 1 y-count)])
            (send dc draw-line 
                  dx
                  (+ dy (* i size-per-cell))
                  (+ dx width)
                  (+ dy (* i size-per-cell))))
          (void))
        width
        height))
  (hb-append
   (apply 
    vc-append
    (for/list ([i (in-range y-count)])
      (cc-superimpose 
       (blank 0 size-per-cell)
       (blank))))
   (vc-append
    (apply 
     hc-append
     (for/list ([i (in-list (list "natural" "symbol" "float"))])
       (define txt (text (format "~a" i) '() 10))
       (cc-superimpose (blank size-per-cell 0)
                       (refocus
                        (hbl-append
                         txt
                         (blank))
                        txt))))
    
    (let loop ([i 0]
               [pict base])
      (cond
        [(= i num-points) pict]
        [else
         (define (i->xy v k)
           (define i
             (match v
               [(? exact-integer?) 0]
               [(? char?) 1]
               [(? flonum?) 2]))
           (define j
             (match v
               [(? exact-integer?) (to-nat natural/e v)]
               [(? char?) (to-nat char/e v)]
               [(? flonum?) (to-nat flonum/e v)]))
           (values (* (+ i .5) size-per-cell)
                   (* (+ j .5) size-per-cell)))
         (define this (from-nat prs i))
         (define next (from-nat prs (+ i 1)))
         (define-values (x1 y1) (i->xy this i))
         (define-values (x2 y2) (i->xy next (+ i 1)))
         (define this-p 
           (text (~a #:max-width 6 this)))
         (define index-p (text (format "~a" i)))
         (define index this-p)
         (define pict+index
           (pin-over pict
                     (- x1 (/ (pict-width index) 2))
                     (- y1 (/ (pict-height index) 2))
                     index))
         (loop (+ i 1)
               (if (and arrows? (i . < . last-arrow))
                   (pin-arrow-line
                    #:color "blue"
                    #:alpha 0.5
                    #:under? #t
                    arrow-head-size
                    pict+index
                    pict+index
                    (λ (a b) (values x1 (+ y1 (pict-height index))))
                    pict+index
                    (λ (a b) (values x2 (+ y2 (pict-height index)))))
                   pict+index))])))))


(define (pair-pict) (box-cons-pict))
(define (box-cons-pict) (grid cons/e 5 24 200 12))
(define (cantor-cons-pict) (grid cantor-cons/e 5 14 200 12))

(define (cantor-cons/e e1 e2)
  (cons/e e1 e2 #:ordering 'diagonal))

(define (square x)(x . * . x))
(define (weird-cons/e e1 e2)
  (map/e (λ (n) 
           (define flroot (integer-sqrt n))
           (define p1 (n . - . (square flroot)))
           (cons p1
                 (flroot . - . (quotient (p1 . + . 1) 2))))
         (λ (n)(error 'weird-cons-undefined))
         natural/e))

(define (search-invert f)
  (λ (n)
    (let/ec k
      (for ([t (in-enum (cons/e natural/e natural/e))])
        (when (equal? n (f t))
          (k t))))))
(define (exp-cons/e e1 e2)
  (define (exp-pair xy)
    (define x (car xy))
    (define y (cdr xy))
    (((expt 2 x) . * . ((2 . * . y) . + . 1)) . - . 1))
  (map/e (search-invert exp-pair)
         exp-pair
         natural/e))
(define (grid cons/e count num-points size arrow-head-size)
  (gen-grid cons/e count num-points size arrow-head-size #:arrows? #t))

(define (gen-grid cons/e count num-points size arrow-head-size #:arrows? arrows?)
  (define prs (cons/e natural/e natural/e))
  (define base
    (dc (λ (dc dx dy)
          (for ([i (in-range 1 count)])
            (send dc draw-line 
                  (+ dx (* i (/ size count)))
                  dy
                  (+ dx (* i (/ size count)))
                  (+ dy size))
            (send dc draw-line 
                  dx
                  (+ dy (* i (/ size count)))
                  (+ dx size)
                  (+ dy (* i (/ size count))))))
        size
        size))
  (hb-append
   (apply 
    vc-append
    (for/list ([i (in-range count)])
      (define txt (text (format "~a" i)))
      (cc-superimpose 
       (blank 0 (/ size count))
       (refocus (vc-append
                 txt
                 (if (= i (- count 1))
                     (text "⋮")
                     (blank)))
                txt))))
   (vc-append
    (apply 
     hc-append
     (for/list ([i (in-range count)])
       (define txt (text (format "~a" i)))
       (cc-superimpose (blank (/ size count) 0)
                       (refocus
                        (hbl-append
                         txt
                         (if (= i (- count 1))
                             (text " ⋯")
                             (blank)))
                        txt))))
    
    (let loop ([i 0]
               [pict base])
      (cond
        [(= i num-points) pict]
        [else
         (define (ij->xy i j)
           (values (* (+ i .5) (/ size count))
                   (* (+ j .5) (/ size count))))
         (define this (from-nat prs i))
         (define next (from-nat prs (+ i 1)))
         (define-values (x1 y1) (ij->xy (car this) (cdr this)))
         (define-values (x2 y2) (ij->xy (car next) (cdr next)))
         (define index (text (format "~a" i)))
         (loop (+ i 1)
               (if arrows?
                   (pin-arrow-line
                    arrow-head-size
                    pict
                    pict
                    (λ (a b) (values x1 y1))
                    pict
                    (λ (a b) (values x2 y2)))
                   (pin-over pict
                             (- x1 (/ (pict-width index) 2))
                             (- y1 (/ (pict-height index) 2))
                             index)))])))))


(define-syntax-rule
  (to-count exp)
  (values (format-it 'exp) exp))
(define (format-it exp)
  (define sp (open-output-string))
  (parameterize ([pretty-print-columns 24])
    (pretty-write exp sp))
  (get-output-string sp))

(define-values (fair-exp fair/e)
  (to-count (cons/e (cons/e natural/e natural/e)
                    (cons/e natural/e natural/e))))

(define-values (unfair-exp unfair/e)
  (to-count (cons/e 
             natural/e
             (cons/e 
              natural/e
              (cons/e
               natural/e
               natural/e)))))

(define num-enumerated 4000)
(define (count-em enum)
  (map (λ (x) (apply max x)) 
       (transpose (map flatten (enum->list enum num-enumerated)))))
(define (transpose l) (apply map list l))
(define unfair-cons (count-em unfair/e))
(define fair-cons (count-em fair/e))
(define (render-fair/unfair max/min which)
  (code (number->string (apply max/min which))))

(define max-unfair (render-fair/unfair max unfair-cons))
(define min-unfair (render-fair/unfair min unfair-cons))
(define max-fair (render-fair/unfair max fair-cons))
(define min-fair (render-fair/unfair min fair-cons))


(define (render-enumerations lst)
  (define strs (for/list ([ele (in-list lst)])
                 (format "~v" ele)))
  (define max-str-w (apply max (map string-length strs)))
  (when (< rendered-enumeration-width max-str-w)
    (error 'render-enumerations "one of the strings is wider than a line"))
  (define columns (+ 1 (floor
                        (/ (- rendered-enumeration-width max-str-w)
                           (+ max-str-w (string-length column-gap))))))
  (define (take/min lst pos) 
    (if (< (length lst) pos) lst (take lst pos)))
  (define (drop/min lst pos)
    (if (< (length lst) pos) '() (drop lst pos)))
  (define line-strings
    (let loop ([strs strs])
      (cond
        [(null? strs) '()]
        [else
         (define this-line (take/min strs columns))
         (cons (string-append (apply
                               string-append
                               (add-between
                                (for/list ([ele (in-list this-line)])
                                  (pad-to max-str-w ele))
                                column-gap))
                              "\n")
               (loop (drop/min strs columns)))])))
  
  ;; this drops leading quotes, which doesn't seem good
  ;; because the line-breaking code above counts the leading
  ;; quotes. Should really reconcile theses two
  (apply typeset-code line-strings))

(define (pad-to w str)
  (cond
    [(< (string-length str) w)
     (string-append str (build-string (- w (string-length str))
                                      (λ (_) #\space)))]
    [else str]))

(define column-gap "    ")
(define rendered-enumeration-width 55)

(define-syntax-rule 
  (enum-example stx count)
  (render-enumerations (enum->list stx count)))

(define (except/e* enum lst)
  (let loop ([lst lst]
             [enum enum])
    (cond
      [(null? lst) enum]
      [else (loop (cdr lst) (except/e enum (car lst)))])))

(define-syntax-rule
  (define-lon/e/dup x1 x2 expr)
  (begin (define x1 (racketblock expr))
         (define x2 expr)))

(define-lon/e/dup lon/e-code lon/e
  (letrec ([lon/e
            (or/e (fin/e null)
                  (cons/e (below/e +inf.0)
                          (delay/e lon/e)))])
    lon/e))

(define-lon/e/dup lon2/e-code lon2/e
  (or/e (single/e '())
        (dep/e (below/e +inf.0)
               (λ (len)
                 (define enums
                   (for/list ([i (in-range (+ len 1))])
                     (below/e +inf.0)))
                 (apply list/e enums)))))

(module+ main 
  (hc-append 60 (disj-sum-pict/bad) (disj-sum-pict/good)))
