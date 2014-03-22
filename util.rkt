#lang racket/base
(require scribble/core 
         scribble/manual
         racket/list
         rackunit)
(provide raw-latex a-quote
         racketblock/define
         add-commas)

(define (raw-latex . args)
  (element (style "relax" '(exact-chars))
           args))

(define (a-quote . args)
  (nested-flow (style 'inset '()) (list (paragraph (style #f '()) args))))

(define-syntax-rule
  (racketblock/define exp)
  (begin (racketblock exp)
         exp))

(define (add-commas n)
  (define s (format "~a" n))
  (define comma-every 3)
  (define cs
    (let loop ([chars (reverse (string->list s))])
      (cond
        [(<= (length chars) comma-every) chars]
        [else 
         (append (take chars comma-every)
                 '(#\,)
                 (loop (drop chars comma-every)))])))
  (apply string (reverse cs)))

(check-equal? (add-commas 1) "1")
(check-equal? (add-commas 12) "12")
(check-equal? (add-commas 123) "123")
(check-equal? (add-commas 1234) "1,234")
(check-equal? (add-commas 12345) "12,345")
(check-equal? (add-commas 123456789) "123,456,789")
(check-equal? (add-commas 1234567890) "1,234,567,890")
