#lang racket/base

(require racket/sandbox
         scribble/eval)

(provide interact)

(define enum-evaluator
  (call-with-trusted-sandbox-configuration 
   (λ ()
     (parameterize ([sandbox-output 'string]
                    [sandbox-error-output 'string])
       (make-evaluator #:requires '(redex/private/enumerator)
                       'racket)))))

(define-syntax-rule (interact code)
  (interaction #:eval enum-evaluator
               code))