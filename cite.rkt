#lang racket/base

(require scriblib/autobib)
(provide (except-out (all-defined-out) fpca jfp types icfem waaapl))
(define-cite ~cite citet generate-bibliography)

(define fpca
  "International Conference on Functional Programming Languages And Computer Architecture")
(define jfp
  "Journal of Functional Programming")
(define types
  "Workshop of the Working Group Types")
(define icfem
  "International Conference on Formal Engineering Methods and Software Engineering")
(define waaapl
  "Workshop on Algorithmic Aspects of Advanced Programming Languages")
(define esop
  "European Symposium on Programming")
(define tphols
  "Theorem Proving in Higher Order Logics")
(define popl
  "Symposium on Principles of Programming Languages")
(define scheme-workshop 
  "Scheme and Functional Programming")
(define jar 
  "Journal of Automated Reasoning")

(define sfp2009-kf
  (make-bib
   #:author (authors "Casey Klein" "Robert Bruce Findler")
   #:title "Randomized Testing in PLT Redex"
   #:location (proceedings-location scheme-workshop #:pages '(26 36))
   #:date "2009"))
                                
(define run-your-research
  (make-bib
   #:author (authors "Casey Klein" "John Clements" "Christos Dimoulas"
                     "Carl Eastlund" "Matthias Felleisen" "Matthew Flatt"
                     "Jay A. McCarthy" "Jon Rafkind" "Sam Tobin-Hochstadt" 
                     "Robert Bruce Findler")
   #:title "Run Your Research: On the Effectiveness of Lightweight Mechanization"
   #:location (proceedings-location popl)
   #:date 2012))


(define delim-cont-cont
  (make-bib
   #:author (authors "Asumu Takikawa" "T. Stephen Strickland" "Sam Tobin-Hochstadt")
   #:title "Constraining Delimited Control with Contracts"
   #:location (proceedings-location esop
                                    #:pages '(229 248))
   #:date 2013))

(define list-machine
  (make-bib
   #:author (authors "Andrew W. Appel" "Robert Dockins" "Xavier Leroy")
   #:title "A list-machine benchmark for mechanized metatheory"
   #:location (journal-location jar
                       #:volume 49
                       #:number 3
                       #:pages '(453 491))
   #:date 2012))

