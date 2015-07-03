#lang racket

#|

This script find the benchmark/generator
combinations where the ratio of the error
to the actual value is greater than 1/2.

|#

(require redex/benchmark/private/graph-data
         racket/runtime-path)

(define-runtime-path d "all")

(define-values (data _)
  (process-data
   (extract-data/log-directory d)
   (extract-names/log-directory d)))

(define rel-errs
  (sort (for/list ([d (in-list data)])
          (match d
            [(list name type val err)
             (list (/ err val) name type)]))
        > #:key car))

(define bad-ones
  (filter (match-lambda
            [(list rel-err name type)
             (rel-err . > . 0.5)])
          rel-errs))

(for ([one (in-list bad-ones)])
  (displayln one))