#lang racket/base

(require scriblib/autobib)
(provide (except-out (all-defined-out) fpca jfp types icfem waaapl)
         in-bib)
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
(define hosc 
  "Higher-Order and Symbolic Computation")
(define tools
  "International Conference on Objects, Models, Components, Patterns")
(define pldi
  "Programming Language Design and Implementation")
(define frocos
  "Frontiers of Combining Systems")
(define icfp
  "International Conference on Functional Programming")
(define iclp
  "International Conference on Logic Programming")
(define ciclops
  "International Colloquium on Implementation of Constraint Logic Programming Systems")
(define tose
  "IEEE Transactions of Software Engineering")
(define rta
  "International Conference on Rewriting Techniques and Applications")
(define ml
  "Workshop on ML")
(define haskell
  "Haskell Symposium")
(define cpp
  "International Conference on Certified Programs and Proofs")
(define cacm
  "Communications of the ACM")
(define tcs
  "Theoretical Computer Science")

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

(define redex-book
  (make-bib
   #:title "Semantics Engineering with PLT Redex"
   #:author (authors "Matthias Felleisen" "Robert Bruce Findler" "Matthew Flatt")
   #:location (book-location #:publisher "MIT Press")
   #:date 2009))

(define redex-rta
  (make-bib
   #:title "A Visual Environment for Developing Context-Sensitive Term Rewriting Systems"
   #:author (authors "Jacob Matthews" "Robert Bruce Findler" "Matthew Flatt" "Matthias Felleisen")
   #:location (proceedings-location rta)
   #:date 2004))
   
(define scife
  (make-bib
   #:author (authors "Ivan Kuraj" "Viktor Kuncak")
   #:title "SciFe: Scala Framework for Efficient Enumeration of Data Structures with Invariants"
   #:date 2014
   #:location (proceedings-location "Scala Workshop")))

(define bit-monad-transformers
  (make-bib
   #:title "Backtracking, Interleaving, and Terminating Monad Transformers"
   #:author (authors "Oleg Kiselyov" "Chung-chieh Shan" "Daniel P. Friedman" "Amr Sabry")
   #:location (proceedings-location icfp)
   #:date 2005))


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

(define racket-virtual-machine
  (make-bib
   #:author (authors "Casey Klein" "Robert Bruce Findler" "Matthew Flatt")
   #:title "The Racket virtual machine and randomized testing"
   #:location (journal-location hosc)
   #:date 2013))

(define contract-driven-testing-of-javascript-code
  (make-bib
   #:title "Contract-Driven Testing of JavaScript Code"
   #:author (authors "Phillip Heidegger" "Peter Thiemann")
   #:location (proceedings-location tools)
   #:date 2010))

(define quickcheck
  (make-bib
   #:title "QuickCheck: a lightweight tool for random testing of Haskell programs"
   #:author (authors "Koen Classen" "John Hughes")
   #:date 2000
   #:location (proceedings-location icfp)))

(define dart
  (make-bib 
   #:title "DART: Directed Automated Random Testing"
   #:author (authors "Patrice Godefroid" "Nils Klarlund" "Koushik Sen")
   #:date 2005
   #:location (proceedings-location pldi)))

(define isabelle-testing
  (make-bib
   #:title "Automatic Proof and Disproof in Isabelle/HOL"
   #:author (authors "Jasmin Christian Blanchette" "Lukas Bulwahn" "Tobias Nipkow")
   #:date 2011
   #:location (proceedings-location frocos)))

(define bijective-term-encodings
  (make-bib
   #:title "Bijective Term Encodings"
   #:author "Paul Tarau"
   #:date 2011
   #:location (proceedings-location ciclops)))

(define inverting-cantor-n-tupling
  (make-bib
   #:title "Deriving a Fast Inverse of the Generalized Cantor N-tupling Bijection"
   #:author "Paul Tarau"
   #:date 2012
   #:location (proceedings-location iclp)))

(define small-scope-hypothesis
  (make-bib
   #:title "Evaluating the “Small Scope Hypothesis”"
   #:author (authors "Alexandr Andoni" "Dumitru Daniliuc" "Sarfraz Khurshid" "Darko Marinov")
   #:date 2002
   #:location (proceedings-location popl)))

(define an-evaluation-of-random-testing
  (make-bib
   #:title "An Evaluation of Random Testing"
   #:author (authors "Joe W. Duran" "Simeon C. Ntafos")
   #:date 1984
   #:location (journal-location tose #:volume 10 #:number 4)))

(define counting-and-generating-lambda-terms
  (make-bib 
   #:title "Counting and generating lambda terms"
   #:author (authors "Katarzyna Grygiel" "Pierre Lescanne")
   #:date 2013
   #:location (journal-location jfp #:volume 23 #:number 5)))

(define fast-and-sound-random-generation
  (make-bib
   #:title "Fast and Sound Random Generation for Automated Testing and Benchmarking in Objective Caml"
   #:author (authors "Benjamin Canou" "Alexis Darrasse")
   #:date 2009
   #:location (proceedings-location ml)))

(define feat
  (make-bib
   #:title "Feat: Functional Enumeration of Algebraic Types"
   #:author (authors "Jonas Duregård" "Patrik Jansson" "Meng Wang")
   #:location (proceedings-location haskell)
   #:date 2012))

(define every-bit-counts
  (make-bib
   #:title "Every Bit Counts: The binary representation of typed data and programs"
   #:author (authors "Andrew J. Kennedy" "Dimitrios Vytiniotis")
   #:location (journal-location jfp #:volume 22 #:number "4-5")
   #:date 2010))

(define small-check
  (make-bib
   #:title "SmallCheck and Lazy SmallCheck: Automatic Exhaustive Testing for Small Values"
   #:author (authors "Colin Runciman" "Matthew Naylor" "Fredrik Lindblad")
   #:location (proceedings-location haskell)
   #:date 2008))

(define one-roof
  (make-bib
   #:title "The New Quickcheck for Isabelle: Random, Exhaustive and Symbolic Testing Under One Roof"
   #:author "Lukas Bulwahn"
   #:location (proceedings-location cpp)
   #:date 2012))

(define generating-random-lambda-terms
  (make-bib
   #:title "Testing an Optimising Compiler by Generating Random Lambda Terms"
   #:author "Michał H. Pałka"
   #:location (dissertation-location
               #:institution "Chalmers University of Technology and Göteborg University"
               #:degree "Licentiate of Philosophy")
   #:date 2012))

(define finding-and-understanding-bugs-in-c-compilers
  (make-bib
   #:title "Finding and Understanding Bugs in C Compilers"
   #:author (authors "Xuejun Yang" "Yang Chen" "Eric Eide" "John Regehr")
   #:date 2011
   #:location (proceedings-location pldi)))

(define palka-workshop
  (make-bib
   #:author (authors "Michał H. Pałka" "Koen Claessen"
                     "Alejandro Russo" "John Hughes")
   #:title "Testing an Optimising Compiler by Generating Random Lambda Terms"
   #:location (proceedings-location "International Workshop on Automation of Software Test")
   #:date 2011))

(define fuzzing-unix-utils
  (make-bib
   #:title "An Empirical Study of the Reliability of UNIX Utilities"
   #:author (authors "Barton P. Miller" "Lars Fredriksen" "Bryan So")
   #:location (journal-location cacm #:volume 33 #:number 12)
   #:date 1990))

(define elegant-pairing-function
  (make-bib
   #:title "An Elegant Pairing Function"
   #:author "Matthew Szudzik"
   #:url "http://szudzik.com/ElegantPairing.pdf"
   #:date 2006))

(define cantor-n-tupling
  (make-bib
   #:title "On arithmetical first-order theories allowing encoding and decoding of lists"
   #:author (authors "Patrick Cegielski" "Denis Richard")
   #:location (journal-location tcs #:volume 222 #:number "1-2")
   #:date 1999))
