#lang scribble/sigplan

@(require "cite.rkt" 
          "util.rkt"
          scribble/core
          scribble/latex-properties
          (except-in scribble/manual author))

@(define extra-tex-code
   (bytes-append #"\\usepackage{pslatex}\n"
                 #"\\usepackage{inconsolata}\n"
                 #"\\usepackage{savesym}\n"
                 #"\\savesymbol{iint}\n"
                 #"\\savesymbol{iiint}\n"
                 #"\\savesymbol{dddot}\n"
                 #"\\savesymbol{dddot}\n"
                 #"\\savesymbol{ddddot}\n"
                 #"\\savesymbol{overleftrightarrow}\n"
                 #"\\savesymbol{underleftarrow}\n"
                 #"\\savesymbol{underrightarrow}\n"
                 #"\\savesymbol{underleftrightarrow}\n"
                 #"\\savesymbol{ulcorner}\n"
                 #"\\savesymbol{urcorner}\n"
                 #"\\savesymbol{llcorner}\n"
                 #"\\savesymbol{lrcorner}\n"

                 
                 #"\\usepackage{amsmath}\n"
                 #"\\usepackage{amsthm}\n"
                 #"\\usepackage{amsfonts}\n"

                 #"\\usepackage{wrapfig}\n"
                 
                 ;; horrible hack to work around the fact that inconsolata in texlive 2013
                 ;; doesn't have the straight quote character.
                 #"\\savesymbol{textquotesingle}\n"
                 #"\\newcommand{\\textquotesingle}{"
                 #"\\fontfamily{cmtt}\\selectfont{}\\origtextquotesingle}\n"

                 #"\\newtheorem{theorem}{Theorem}\n"
                 
                 ;; map the ℕ character
                 #"\\DeclareUnicodeCharacter{2115}{$\\mathbb{N}$}\n"
                 
                 ;; used for the table of the bugs
                 #"\\newenvironment{IntroWrapFigure}"
                 #"{\\begin{wrapfigure}{r}{4in}}"
                 #"{\\end{wrapfigure}}\n"))

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  Fair Enumeration Combinators
}
@;{
@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]

@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]

@authorinfo["Jay McCarthy"
            "UMass Lowell"
            "jay.mccarthy@gmail.com"]

@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]
}

@(define (abstract-text raw-text?)

   (define (def arg)
     (if raw-text?
         (format "“~a”" arg)
         (emph arg)))

   (define (nth-root-of-n n)
     (if raw-text?
         (case n
           [(2) "the square root of n"]
           [(3) "the cube root of n"]
           [(4) "the fourth root of n"]
           [else (error 'nth-root-of-n "unknown root: ~a" n)])
         @(texmath (format "\\sqrt[~a]{n}" n))))

   (define nth
     (if raw-text?
         "n-th"
         @list{@texmath{n}th}))

   (define n-over-3
     (if raw-text?
         "n/3"
         @texmath{\frac{n}{3}}))
   
   @list{
 Enumerations represented as
 bijections between the natural numbers and elements of some
 given type have recently garnered interest in property-based testing
 because of their efficiency and flexibility as
 counter-example generators. There are, however, many ways of defining
 these bijections, some of which are better than others. 
 This paper offers a new property of enumeration combinators
 called @def{fairness} that identifies enumeration combinators
 that are more suited to property-based testing.
 
Intuitively, the result of a fair combinator indexes into its
argument enumerations equally when constructing its result.
For example, extracting the @nth element from
our enumeration of three-tuples indexes about
@nth-root-of-n[3] elements into each of its
components instead of, say, indexing
@nth-root-of-n[2]
into one and
@nth-root-of-n[4]
into the other two as you would if
a three-tuple were built out of nested pairs. Similarly,
extracting the @nth element from our
enumeration of a three-way union returns an
element that is @n-over-3 into one of the
argument enumerators.

The paper presents a semantics of enumeration
combinators, a theory of fairness, proofs establishing
fairness of our new combinators and that certain
combinations of fair combinators are not fair.

We also report on an evaluation of fairness for the purpose
of finding bugs in operational semantics and type systems.
We implemented a general-purpose enumeration
library for Racket and used it to build generators for
arbitrary Redex grammars. We used an existing benchmark
suite of buggy Redex models to compare the bug finding
capabilities of the original, ad hoc random generator to
generators based on fair and unfair enumeration combinators.
The enumeration using the fair combinators has complementary
strengths to the ad hoc generator (better on short time
scales and worse on long time scales) and using unfair
combinators is worse across the board.
})

@(define (show-abstract)
   (define sp (open-output-string))
   (define max-width 48)
   (define paragraphs
     (for/list ([para (in-list (regexp-split #rx"\n\n" (apply string-append (abstract-text #t))))])
       (filter (λ (x) (not (regexp-match? #rx"^ *$" x)))
               (regexp-split #rx"[\n ]+" para))))

   (define word-count 0)
   
   (for ([words (in-list paragraphs)])
     (define line-width 0)
     (for ([word (in-list words)])
       (set! word-count (+ word-count 1))
       (unless (regexp-match #rx"^ *$" word)
         (display word sp)
         (display " " sp)
         (set! line-width (+ (string-length word) line-width))
         (when (> line-width max-width)
           (set! line-width 0)
           (newline sp))))
     (newline sp)
     (newline sp))

   (printf "~a words\n" word-count)
   
   (display
    (regexp-replace*
     #rx"\n\n\n"
     (regexp-replace*
      #rx" \n"
      (get-output-string sp)
      "\n")
     "\n\n")))
   
   

@(apply abstract (abstract-text #f))

@include-section["intro.scrbl"]

@include-section["combinators.scrbl"]

@include-section["fair-informal.scrbl"]

@include-section["fair-combinators.scrbl"]

@include-section["fair-formal.scrbl"]

@;; comment this out for now because it causes problems at the latex somehow
@;@include-section["redex-enumeration.scrbl"]

@include-section["evaluation.scrbl"]

@include-section["related.scrbl"]

@include-section["future.scrbl"]

@include-section["conclusion.scrbl"]

@generate-bibliography[]

@include-section["appendix.scrbl"]
