#lang scribble/base

@(require "bug-info.rkt"
          racket/pretty
          racket/port
          racket/list)

;; mainly made for my own sanity to help with writing 
;; benchmark section
;; but maybe a reduced, formatting-fixed, version would
;; go in the paper
;; (how do you get these to format well??...)

@[tabular #:style 'boxed #:sep @hspace[1]
          (cons
           (list @bold{model}
                 @bold{bug}
                 @bold{model LOC}
                 @bold{bug description}
                 @bold{bug category}
                 @bold{counterexample}
                 @bold{counterexample size})
           (for/list ([t/n (in-list all-types/nums)])
             (define type (first t/n))
             (define num (second t/n))
             (list (symbol->string type) 
                   (number->string num)
                   (get-line-count type)
                   (get-error type num)
                   (symbol->string (get-category type num))
                   (verbatim
                    (with-output-to-string 
                     (λ ()
                       (parameterize ([pretty-print-columns 40])
                         (pretty-display (get-counterexample type num)
                                         (current-output-port))))))
                   (number->string (get-counterexample-size type num))
                   #;(verbatim
                      (get-diff type num)))))]