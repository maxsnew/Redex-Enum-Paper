#lang racket
(require redex/private/enumerator
         pict
         scribble/manual)

(provide pair-pict 
         grid gen-grid
         unfair-exp fair-exp num-enumerated
         max-unfair min-unfair max-fair min-fair
         render-enumerations
         enum-example
         except/e*
         fin/e)

(define (pair-pict) (grid 5 12 200 12))

(define (grid count num-points size arrow-head-size)
  (gen-grid cons/e count num-points size arrow-head-size))

(define (gen-grid cons/e count num-points size arrow-head-size #:arrows? arrows?)
  (define prs (cons/e nat/e nat/e))
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
         (define this (decode prs i))
         (define next (decode prs (+ i 1)))
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
  (to-count (cons/e (cons/e nat/e nat/e)
                    (cons/e nat/e nat/e))))

(define-values (unfair-exp unfair/e)
  (to-count (cons/e 
             nat/e
             (cons/e 
              nat/e
              (cons/e
               nat/e
               nat/e)))))
  
(define num-enumerated 4000)
(define (count-em enum)
  (map (λ (x) (apply max x)) 
       (transpose (map flatten (approximate enum num-enumerated)))))
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
                           (+ max-str-w 3)))))
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
                                "    "))
                              "\n")
               (loop (drop/min strs columns)))])))
  (apply typeset-code line-strings))

(define (pad-to w str)
  (cond
    [(< (string-length str) w)
     (string-append str (build-string (- w (string-length str))
                                      (λ (_) #\space)))]
    [else str]))

(define rendered-enumeration-width 45)

(define-syntax-rule 
  (enum-example stx count)
  (render-enumerations (approximate stx count)))

(define (except/e* enum lst)
  (let loop ([lst lst]
             [enum enum])
    (cond
      [(null? lst) enum]
      [else (loop (cdr lst) (except/e enum (car lst)))])))