#lang racket/base
(require scribble/core 
         scribble/manual
         racket/list
         racket/port
         rackunit
         scribble/decode
         (for-syntax racket/base))
(provide raw-latex a-quote
         texmath
         racketblock/define
         add-commas
         extract-pick-an-index
         theorem
         proof
         definition
         qed
         assert)

(define-syntax (assert stx)
  (syntax-case stx ()
    [(_ e)
     #`(assert/proc '#,(syntax-source stx) #,(syntax-line stx) (λ () e) 'e)]))
(define (assert/proc source line thunk exp)
  (unless (thunk)
    (error 'assert "assertion ~a:~a failed:\n  ~s" source line exp)))

(define (texmath arg)
  (raw-latex (string-append "$" arg "$")))

(define (raw-latex . args)
  (element (style "relax" '(exact-chars))
           args))

(define (a-quote . args)
  (nested-flow (style 'inset '()) (list (paragraph (style #f '()) args))))

(define-syntax-rule
  (racketblock/define exp ...)
  (begin (racketblock exp ...)
         exp ...))

(define (add-commas n #:hyphens? [hyphens? #f])
  (define s (format "~a" n))
  (define comma-every 3)
  (define cs
    (let loop ([chars (reverse (string->list s))])
      (cond
        [(<= (length chars) comma-every) chars]
        [else 
         (append (take chars comma-every)
                 (if hyphens?
                     '(#\- #\\ #\,)
                     '(#\,))
                 (loop (drop chars comma-every)))])))
  (apply string (reverse cs)))

(check-equal? (add-commas 1) "1")
(check-equal? (add-commas 12) "12")
(check-equal? (add-commas 123) "123")
(check-equal? (add-commas 1234) "1,234")
(check-equal? (add-commas 12345) "12,345")
(check-equal? (add-commas 123456789) "123,456,789")
(check-equal? (add-commas 123456789 #:hyphens? #t) "123,\\-456,\\-789")
(check-equal? (add-commas 1234567890) "1,234,567,890")

(define (extract-pick-an-index)
  (define src (collection-file-path "generate-term.rkt" "redex" "private"))
  (call-with-input-file src
    (λ (port)
      (let loop ()
        (define l (read-line (peeking-input-port port)))
        (cond
          [(eof-object? l) (error 'methodology "didn't find pick-an-index")]
          [(regexp-match #rx";; +pick-an-index +:.*Nat" l)
           (define pp (peeking-input-port port))
           (port-count-lines! pp)
           (read pp)
           (read pp)
           (define-values (line col pos) (port-next-location pp))
           (for/list ([i (in-range line)])
             (string-append (read-line port) "\n"))]
          [else
           (read-line port)
           (loop)])))))

(define-syntax (define-environment stx)
  (syntax-case stx ()
    [(_ id)
     (identifier? #'id)
     #'(define-environment id #f)]
    [(_ id neg-space?)
     #`(define (id . args) (environment/proc 'id args neg-space?))]))
(define (environment/proc id args neg-space?)
  (compound-paragraph (style (symbol->string id) '())
                      (list (decode-compound-paragraph
                             (if neg-space?
                                 (cons (element (style "vspace" '(exact-chars)) "-.15in")
                                       args)
                                 args)))))

(define-environment theorem)
(define-environment proof)
(define-environment definition)
(define qed (element (style "qed" '()) '()))

