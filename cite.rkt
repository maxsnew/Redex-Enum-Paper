#lang racket/base

(require scriblib/autobib)
(provide (except-out (all-defined-out) fpca jfp types icfem waaapl))
(define-cite ~cite citet generate-bibliography)

(define fpca
  "Proc. International Conference on Functional Programming Languages And Computer Architecture")
(define jfp
  "Journal of Functional Programming")
(define types
  "Proc. Workshop of the Working Group Types")
(define icfem
  "Proc. International Conference on Formal Engineering Methods and Software Engineering")
(define waaapl
  "Proc. Workshop on Algorithmic Aspects of Advanced Programming Languages")
(define esop
  "Proc. European Symposium on Programming")
(define tphols
  "Proc. Theorem Proving in Higher Order Logics")
(define popl
  "Proc. Symposium on Principles of Programming Languages")

