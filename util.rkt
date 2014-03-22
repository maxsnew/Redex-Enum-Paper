#lang racket/base
(require scribble/core)
(provide raw-latex a-quote)

(define (raw-latex . args)
  (element (style "relax" '(exact-chars))
           args))

(define (a-quote . args)
  (nested-flow (style 'inset '()) (list (paragraph (style #f '()) args))))
