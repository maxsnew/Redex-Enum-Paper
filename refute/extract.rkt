#lang racket
(require racket/runtime-path
         scribble/core
         scribble/manual)

(provide dart.hs dart.rkt isabelle.hs isabelle.rkt)

(define (combine-code lines)
  (apply verbatim lines))

(define (extract filename)
  (combine-code
   (remove-leading-spaces
    (call-with-input-file filename
      (λ (port)
        (let loop ([started? #f])
          (define l (read-line port))
          (cond
            [(eof-object? l)
             (error 'extract "eof too soon for ~a" filename)]
            [(and started?
                  (regexp-match #rx"STOP" l))
             '()]
            [(and (not started?)
                  (regexp-match #rx"START" l))
             (loop #t)]
            [started?
             (list* l "\n" (loop #t))]
            [else
             (loop #f)])))))))

(define (remove-leading-spaces lst)
  (define without-trailing-space
    (for/list ([s (in-list lst)])
      (regexp-replace #rx" +$" s "")))
  (define counts
    (for/list ([line (in-list without-trailing-space)])
      (cond
        [(regexp-match #rx"^ *$" line) +inf.0]
        [else
         (string-length 
          (list-ref (regexp-match #rx"(^ *)" line) 1))])))
  (define smallest (apply min counts))
  (cond
    [(= smallest +inf.0) without-trailing-space]
    [else
     (for/list ([l (in-list without-trailing-space)])
       (substring l
                  (inexact->exact smallest)
                  (string-length l)))]))

(define-runtime-path dart-authors-conjecture.hs "dart-authors-conjecture.hs")
(define-runtime-path dart-authors-conjecture.rkt "dart-authors-conjecture.rkt")
(define-runtime-path isabelle-authors-conjecture.hs "isabelle-authors-conjecture.hs")
(define-runtime-path isabelle-authors-conjecture.rkt "isabelle-authors-conjecture.rkt")

(define dart.hs (extract dart-authors-conjecture.hs))
(define dart.rkt (extract dart-authors-conjecture.rkt))
(define isabelle.hs (extract isabelle-authors-conjecture.hs))
(define isabelle.rkt (extract isabelle-authors-conjecture.rkt))
