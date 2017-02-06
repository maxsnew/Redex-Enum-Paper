#lang at-exp racket
(require data/enumerate/lib
         pict
         redex/pict
         scribble/manual
         math/number-theory
         (only-in data/enumerate/private/core binary-biased-cons/e))

(provide pair-pict cantor-cons-pict
         disj-sum-pict/good disj-sum-pict/bad
         biased-cons-pict
         grid gen-grid
         unfair-exp fair-exp num-enumerated
         max-unfair min-unfair max-fair min-fair
         render-enumerations
         enum-example
         except/e*
         fin/e
         lon/e-code lon/e
         lon2/e-code lon2/e

         pair-1/1-tex pair-m/n-tex)

(define (disj-sum-pict/good)
  (gen-table or/e 8 24 30 8 #:arrows? #t))

(define (disj-sum-pict/bad)
  (define (bad-disj-sum/e a b c)
    (or/e a (or/e b c)))
  (gen-table bad-disj-sum/e 8 32 30 8 #:arrows? #t #:last-arrow 15))

(define (gen-table or/e y-count num-points size-per-cell arrow-head-size
                   #:arrows? arrows? #:last-arrow [last-arrow +inf.0])

  (define font-size 9)
  
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
     (for/list ([i (in-list (list "nat" "sym" "float"))])
       (define txt (text (format "~a" i) '() font-size))
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
         (define this-p (text (~a #:max-width 6 this) '() font-size))
         (define pict+index
           (pin-over pict
                     (- x1 (/ (pict-width this-p) 2))
                     (- y1 (/ (pict-height this-p) 2))
                     this-p))
         (loop (+ i 1)
               (if (and arrows? (i . < . last-arrow))
                   (pin-arrow-line
                    #:color "blue"
                    #:alpha 0.5
                    #:under? #t
                    arrow-head-size
                    pict+index
                    pict+index
                    (λ (a b) (values x1 (+ y1 (pict-height this-p))))
                    pict+index
                    (λ (a b) (values x2 (+ y2 (pict-height this-p)))))
                   pict+index))])))))

(define (pair-pict) (box-cons-pict))
(define (box-cons-pict) (grid cons/e 5 24 180 10))
(define (cantor-cons-pict) (grid cantor-cons/e 5 14 180 10))
(define (biased-cons-pict)
  (gen-grid (λ (x y) (binary-biased-cons/e x 2 y 1)) 25 6 149 420 6 #:arrows? #t))

(define (cantor-cons/e e1 e2)
  (cons/e e1 e2 #:ordering 'diagonal))

(define (grid cons/e count num-points size arrow-head-size)
  (gen-grid cons/e count count num-points size arrow-head-size #:arrows? #t))

(define (gen-grid cons/e count-x count-y num-points size-x arrow-head-size #:arrows? arrows?)
  (define size-y (* count-y (/ size-x count-x)))
  (define prs (cons/e natural/e natural/e))
  (define font-size 9)
  (define base
    (dc (λ (dc dx dy)
          (for ([i (in-range 1 count-x)])
            (send dc draw-line 
                  (+ dx (* i (/ size-x count-x)))
                  dy
                  (+ dx (* i (/ size-x count-x)))
                  (+ dy size-y)))
          (for ([i (in-range 1 count-y)])
            (send dc draw-line 
                  dx
                  (+ dy (* i (/ size-y count-y)))
                  (+ dx size-x)
                  (+ dy (* i (/ size-y count-y))))))
        size-x
        size-y))
  (hb-append
   (apply
    vc-append
    (for/list ([i (in-range count-y)])
      (define txt (text (format "~a" i) '() font-size))
      (cc-superimpose 
       (blank 0 (/ size-y count-y))
       (refocus (vc-append
                 txt
                 (if (= i (- count-y 1))
                     (text "⋮" '() font-size)
                     (blank)))
                txt))))
   (vc-append
    (apply 
     hc-append
     (for/list ([i (in-range count-x)])
       (define txt (text (format "~a" i) '() font-size))
       (cc-superimpose (blank (/ size-x count-x) 0)
                       (refocus
                        (hbl-append
                         txt
                         (if (= i (- count-x 1))
                             (text " ⋯" '() font-size)
                             (blank)))
                        txt))))
    
    (let loop ([i 0]
               [pict base])
      (cond
        [(= i num-points) pict]
        [else
         (define (ij->xy i j)
           (values (* (+ i .5) (/ size-x count-x))
                   (* (+ j .5) (/ size-y count-y))))
         (define this (from-nat prs i))
         (define next (from-nat prs (+ i 1)))
         (define-values (x1 y1) (ij->xy (car this) (cdr this)))
         (define-values (x2 y2) (ij->xy (car next) (cdr next)))
         (define index (text (format "~a" i) '() font-size))
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
         (define x2 (let () expr x2))))

(define-lon/e/dup lon/e-code lon/e
  (define lon/e
    (or/e (fin/e null)
          (cons/e (below/e +inf.0)
                  (delay/e lon/e)))))

(define-syntax-rule
  (define-lon/e/dup/2 x1 x2 expr)
  (begin (define x1 (racketblock expr))
         (define x2 expr)))

(define-lon/e/dup/2 lon2/e-code lon2/e
  (or/e (single/e '())
        (dep/e (below/e +inf.0)
               (λ (len)
                 (define enums
                   (for/list ([i (in-range (+ len 1))])
                     (below/e +inf.0)))
                 (apply list/e enums)))))

(module+ main 
  (hc-append 60 (disj-sum-pict/bad) (disj-sum-pict/good)))

(define-syntax-rule
  (define/txt id1 (id2 args ...) body ...)
  (begin
    (define id1 (to-tex 'body ...))
    (define (id2 args ...) body ...)))

(define (to-tex . defs+sexps)
  (define defs (reverse (cdr (reverse defs+sexps))))
  (define body (last defs+sexps))
  (define (def-to-tex def include-where?)
    (match def
      [`(define ,id ,expr)
       @~a{\multicolumn{2}{r}{
         @(if include-where? @~a{\mbox{\textrm{where~}}} "")
         @id = @(expr-to-tex expr)} \\}]))
  (define (cond-expr-to-tex expr)
    (match expr
      [`(cond [,Q1 ,A1] [,Q2 ,A2])
       @~a{@(expr-to-tex A1) & \mbox{\textrm{if~}} @(expr-to-tex Q1) \\
           @(expr-to-tex A2) & \mbox{\textrm{if~}} @(expr-to-tex Q2) \\}]))
  (define (expr-to-tex expr)
    (let loop ([expr expr])
      (match expr
        [`(,(? infix-op? op) ,a ,b) @~a{@(loop a) @(convert-op op) @(loop b)}]
        [`(,(? infix-op? op) ,a ,b ,more ...) (loop `(,op ,a (,op ,b ,@more)))]
        [`(expt ,a ,b) @~a{{@(loop a)}^{@(loop b)}}]
        [`(cons ,a ,b) @~a{\left\langle @(loop a), @(loop b) \right\rangle}]
        [`(integer-sqrt ,a) (loop `(integer-root ,a 2))]
        [`(integer-root ,a ,b)
         @~a{\left\lfloor
          @(if (equal? b 2)
               @~a{\sqrt{@(loop a)}}
               @~a{\sqrt[@(loop b)]{@(loop a)}})
          \right\rfloor}]
        [`(remainder ,a ,b)
         @~a{{@(loop a)} \bmod {@(loop b)}}]
        [`(quotient ,a ,b)
         @~a{\left\lfloor\frac{@(loop a)}{@(loop b)} \right\rfloor}]
        [`(with-parens ,x) @~a{(@(loop x))}]
        [(? symbol?) (~a expr)]
        [(? real?) (~a expr)])))
  (define (infix-op? x) (member x '(+ - * < >=)))
  (define (convert-op op)
    (cond
      [(equal? op '>=) @~a{\geq}]
      [(equal? op '<=) @~a{\leq}]
      [(equal? op '*) @~a{\cdot}]
      [else (~a op)]))
  (string->bytes/utf-8
   @~a{\[\begin{array}{ll}
       @(cond-expr-to-tex body) \\
       @(apply string-append
               (for/list ([def (in-list defs)]
                          [i (in-naturals)])
                 (def-to-tex def (= i 0))))
       \end{array}\]}))

(define/txt pair-m/n-tex (pair-1/n n z)
  (define r (- z (expt (integer-root z (+ n 1)) (+ n 1))))
  (define s (* (with-parens (- (expt (with-parens (+ (integer-root z (+ n 1)) 1)) n)
                               (expt (integer-root z (+ n 1)) n)))
               (integer-root z (+ n 1))))
  (cond
    [(r . < . s)
     (cons (remainder r (integer-root z (+ n 1)))
           (+ (expt (integer-root z (+ n 1)) n)
              (quotient r (integer-root z (+ n 1)))))]
    [(r . >= . s)
     (cons (integer-root z (+ n 1)) (r . - . s))]))

(define/txt pair-1/1-tex (pair-1/1 z)
  (cond
    [((- z (expt (integer-sqrt z) 2)) . < . (integer-sqrt z))
     (cons (- z (expt (integer-sqrt z) 2)) (integer-sqrt z))]
    [((- z (expt (integer-sqrt z) 2)) . >= . (integer-sqrt z))
     (cons (integer-sqrt z) (- z (expt (integer-sqrt z) 2) (integer-sqrt z)))]))

(define (with-parens x) x)

(module+ test
  (define tests 0)
  (time
   (for* ([n (in-range 1 10)]
          [z (in-range 10000)])
     (set! tests (+ tests 1))
     (define correct (from-nat (binary-biased-cons/e natural/e 1 natural/e n) z))
     (define presented (pair-1/n n z))
     (unless (equal? correct presented)
       (error 'enum-util.rkt "correct ≠ presented, ~s vs ~s; ~s"
              correct presented
              (list n z)))
     (when (= n 1)
       (set! tests (+ tests 1))
       (define presented-1-1 (pair-1/1 z))
       (unless (equal? correct presented-1-1)
         (error 'enum-util.rkt "correct ≠ presented-1-1, ~s vs ~s; ~s"
                correct presented-1-1
                z)))))
  (printf "~a tests passed\n" tests))
