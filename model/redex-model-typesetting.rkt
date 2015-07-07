#lang racket
(require redex
         pict
         "redex-model.rkt")

(provide semantics-figure sr unfair-rule
         mf-name)

(define (w/rewriters/proc thunk)
  
  (define (to-sexp lws)
    (let loop ([lws lws])
      (cond
        [(string? lws) (read (open-input-string lws))]
        [(symbol? lws) lws]
        [(boolean? lws) lws]
        [(number? lws) lws]
        [(list? lws)
         (for/list ([lw (in-list (cdr (reverse (cdr (reverse lws)))))])
           (loop (lw-e lw)))]
        [else (error 'to-sexp "unk ~s\n" lws)])))
  
  (define (ae->pict ae)
    (let loop ([needs-parens? #f]
               [ae ae])
      (match ae
        [`(+ ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (d " + ")
                      (loop #t ae2)))]
        [`(- ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (d " - ")
                      (loop #t ae2)))]
        [`(- ,ae1 ,ae2 ,ae3)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (d " - ")
                      (loop #t ae2)
                      (d " - ")
                      (loop #t ae3)))]
        [`(* ,(? simple? ae1) ,(? simple? ae2))
         (htl-append (loop #t ae1)
                     (loop #t ae2))]
        [`(* ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #t ae1)
                      (d "·")
                      (loop #t ae2)))]
        [`(< ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #f ae1)
                      (d " < ")
                      (loop #f ae2)))]
        [`(>= ,ae1 ,ae2)
         (maybe-add-parens
          needs-parens?
          (htl-append (loop #f ae1)
                      (d " ≥ ")
                      (loop #f ae2)))]
        [`(integer-sqrt ,(? symbol? n))
         (define var (it (format "~a" n)))
         (define line (inset (hline (pict-width var)) 0 1 0 0))
         (define left-side (d "√"))
         (hbl-append (d "⌊")
                     left-side 
                     (lbl-superimpose 
                      (refocus 
                       (lbl-superimpose
                        (lt-superimpose (ghost (inset left-side -2 3 (- (pict-width left-side)) 0))
                                        line)
                        var)
                       var))
                     (d "⌋"))]
        [`(/ ,ae1 2)
         (hbl-append (loop #t ae1) (d "/2"))]
        [`(div ,ae1 ,ae2)
         (hbl-append
          (d "⌊")
          (loop #t ae1)
          (d "/")
          (loop #t ae2)
          (d "⌋"))]
        [`(mod ,ae1 ,ae2)
         (hbl-append
          (loop #t ae1)
          (d "%")
          (loop #t ae2))]
        [`(sqr ,ae)
         (define arg (loop #t ae))
         (hbl-append arg (d "²"))]
        [`(size ,ae)
         (define arg (loop #f ae))
         (hbl-append (left-double-bar) arg (right-double-bar))]
        [`(sum-all ,e ,f)
         (maybe-add-parens
          needs-parens?
          (hbl-append (d "Σ x ∈ ") (loop #t e) (d ". ")
                      (left-double-bar)
                      (loop #t f)
                      (d "(x)")
                      (right-double-bar)))]
        [`(sum-up-to ,e ,f ,n)
         (hbl-append (d "sum_up_to(")
                     (loop #t e)
                     (d ", ")
                     (loop #t f)
                     (d ", ")
                     (loop #t n)
                     (d ")"))]
        [`(min ,ae1 ,ae2)
         (hbl-append (d "min(") (loop #f ae1) (d ",") (loop #f ae2) (d ")"))]
        [(? number?) (d (format "~a" ae))]
        [(? symbol-with-no-underscores?)
         (it (format "~a" ae))]
        [`n_1
         (hbl-append (it "n")
                     (basic-text "1" (non-terminal-subscript-style)))]
        [`n_2
         (hbl-append (it "n")
                     (basic-text "2" (non-terminal-subscript-style)))]
        [`e_1
         (hbl-append (it "e")
                     (basic-text "1" (non-terminal-subscript-style)))]
        [`e_2
         (hbl-append (it "e")
                     (basic-text "2" (non-terminal-subscript-style)))]
        [_ 
         (eprintf "missing ~s\n" ae)
         (blank)])))

  (define (d str) (basic-text str (default-style)))
  (define (basic-text str style) ((current-text) str style (default-font-size)))

  (define (hline w)
    (dc (λ (dc dx dy) (send dc draw-line dx dy (+ dx w) dy))
        w
        0))
  
  (define (maybe-add-parens add? p)
    (cond
      [add? (hbl-append (d "(") p (d ")"))]
      [else p]))
  
  (define (simple? x) (or (number? x) (symbol? x)))
  
  (define (overline p)
    (define line (inset (hline (pict-width p)) 0 0 0 -2))
    (refocus (vc-append line p) p))
  
  (define (symbol-with-no-underscores? x) 
    (and (symbol? x) (not (regexp-match? #rx"_" (symbol->string x)))))
  (define (t str) (text str))
  (define (it str) (text str '(italic . roman)))

  (define (@-rewrite lws)
    (define enum (list-ref lws 2))
    (define n (list-ref lws 3))
    (define v (list-ref lws 4))
    (define T (list-ref lws 5))
    (list "" enum " @ " n " = " v (single-bar) T ""))

  (define (bar/s left? x-off)
    (define pipe (d "|"))
    (define w (* (pict-width pipe) (if x-off 3 3)))
    (define h (pict-height pipe))
    (define descent (pict-descent pipe))
    (define a (pict-ascent pipe))
    (dc (λ (dc dx dy)
          (define pen (send dc get-pen))
          (send dc set-pen "black" 1/2 'solid)
          (define (draw-line x-offset)
            (send dc draw-line
                  (+ dx (/ w 2) x-offset)
                  dy
                  (+ dx (/ w 2) x-offset)
                  (+ dy h)))
          (cond
            [x-off
             (draw-line 0)
             (draw-line (if left? (- x-off) x-off))]
            [else
             (draw-line 0)])
          (send dc set-pen pen))
        w h a descent))

  (define (left-double-bar) (bar/s #f 2))
  (define (right-double-bar) (bar/s #t 2))
  (define (single-bar) (bar/s #f #f))
  
  (define (ae-sym lw)
    (cond
      [(symbol? (lw-e lw)) (ae->pict (lw-e lw))]
      [else (error 'ae-sym "non symbol: ~s" (lw-e lw))]))
  
  (with-compound-rewriters
   (['@ @-rewrite]
    ['@* @-rewrite]
    ['@<- @-rewrite]
    ['dep/e
     (λ (lws)
       (list (list-ref lws 0)
             (basic-text "dep/e " (metafunction-style))
             (list-ref lws 3)
             (list-ref lws 4)
             (list-ref lws 5)))]
    ['inf?
     (λ (lws)
       (define e (list-ref lws 3))
       (define f (list-ref lws 4))
       (define @-rewritten
         (@-rewrite (list '_ '_ e
                          "n"
                          "v"
                          "T")))
       (list "∀ x ∈ " e
             (hbl-append (d ",  ") (left-double-bar))
             f
             (hbl-append (d "(x)")
                         (right-double-bar)
                         (d " = ∞"))))]
    ['fin?
     (λ (lws)
       (define e (list-ref lws 3))
       (define f (list-ref lws 4))
       (define @-rewritten
         (@-rewrite (list '_ '_ e
                          "n"
                          "v"
                          "T")))
       (list "∀ x ∈ "
             e
             (hbl-append (d ",  ") (left-double-bar))
             f
             (hbl-append (d "(x)") (right-double-bar) (d " < ∞"))))]
    ['subst
     (λ (lws)
       (define replace-inside (list-ref lws 2))
       (define x (list-ref lws 3))
       (define new-thing (list-ref lws 4))
       (list "" replace-inside "{" x " := " new-thing "}"))]
    ['×
     (λ (lws)
       (list "⟨" (list-ref lws 2) ", " (list-ref lws 3) "⟩"))]
    ['sum-all
     (λ (lws)
       (define e (list-ref 2))
       (define f (list-ref 3))
       (list "Σ x ∈ " e
             (hbl-append (d ". ") (left-double-bar))
             f
             (hbl-append (d "(x)") (right-double-bar))))]
    ['size
     (λ (lws)
       (list (left-double-bar) (list-ref lws 2) (right-double-bar)))]
    ['unpair
     (λ (lws)
       (list "unpair(" (list-ref lws 2) ", " (list-ref lws 3) ", " (list-ref lws 4) ")"))]
    ['⊕
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (list "λx. " arg1 "(x) ∪ " arg2 "(x)"))]
    ['singleton
     (λ (lws)
       (define n1 (list-ref lws 2))
       (define n2 (list-ref lws 3))
       (list "λx. " n1 "=x ? {" n2 "} : ∅"))]
    ['ae-interp
     (λ (lws)
       (list (ae->pict (to-sexp (lw-e (caddr lws))))))]
    ['even
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "" arg " is even"))]
    ['odd
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "" arg " is odd"))]
    ['sum-up-to
     (λ (lws)
       (define e (list-ref lws 2))
       (define f (list-ref lws 3))
       (define n (list-ref lws 4))
       (list "sum_up_to(" e ", " f ", " n ")"))]
    ['sum-up-to/render
     (λ (lws)
       (define f (list-ref lws 2))
       (define e (list-ref lws 3))
       (define n (list-ref lws 4))
       (list (hbl-append (d "Σ{")
                         (left-double-bar))
             f
             (hbl-append (d "(")
                         (ae->pict 'v)
                         (d ")")
                         (right-double-bar)
                         (d " ")
                         (single-bar)
                         (d " ("))
             e
             (hbl-append (d " @ ")
                         (ae->pict 'i)
                         (d " = ")
                         (ae->pict 'v)
                         (d " ")
                         (single-bar)
                         (d " ")
                         (ae->pict 'T)
                         (d ") and ")
                         (ae->pict 'i)
                         (d " < "))
             n
             (d "}")))]
    ['sum-up-to-find-k
     (λ (lws)
       (define n (list-ref lws 2))
       (define f (list-ref lws 3))
       (define e (list-ref lws 4))
       (define k (list-ref lws 5))
       (list (hbl-append (d "sum_up_to(")
                         (ae-sym e)
                         (d ", ")
                         (ae-sym f)
                         (d ", ")
                         (ae-sym k)
                         (d ") ≤ ")
                         (ae-sym n)
                         (d "< sum_up_to(")
                         (ae-sym e)
                         (d ", ")
                         (ae-sym f)
                         (d ", ")
                         (ae-sym k)
                         (d " + 1)"))))]
    ['Eval-enum (λ (lws) (list "" (list-ref lws 2) ""))]
    ['Eval-bij (λ (lws) (list "" (list-ref lws 2) ""))]
    ['unfair-n->n*n
     (λ (lws)
       (define n (list-ref lws 2))
       (define y (list-ref lws 3))
       (define x (list-ref lws 4))
       (define y-p (ae-sym y))
       (list ""
             n
             (hbl-append
              (d " = 2")
              (lift-above-baseline y-p (/ (pict-height y-p) 3))
              (d "(2"))
             x
             " + 1)"))])
   (with-atomic-rewriter
    '∞ (λ () (d "∞"))
    (thunk))))

(define-syntax-rule (w/rewriters e) (w/rewriters/proc (λ () e)))

(define linebreaking-with-cases1
  '(("map" "below/e")
    ("cons")))

(define linebreaking-with-cases2
  '(("or alt l" "or alt r")
    ("or big l" "or big r")
    ("ex<" "dep inf")
    ("ex≥" "dep fin")
    ("fix" "trace")))

(define-syntax-rule
  (w/fonts e)
  (w/fonts/proc (λ () e)))
(define (w/fonts/proc thunk)
  (define helv-font "Helvetica")
  (define font-size 11)
  (parameterize ([label-font-size font-size]
                 [default-font-size font-size]
                 [metafunction-font-size font-size]
                 [metafunction-style helv-font]
                 [literal-style helv-font]
                 [grammar-style helv-font])
    (thunk)))

(define (semantics-figure)
  (w/rewriters
   (w/fonts
    (vc-append
     20
     (ht-append 
      60
      (inset (frame (inset (render-language L #:nts '(e n+ v n i j)) 4)) 4)
      (some-rules linebreaking-with-cases1))
     (some-rules linebreaking-with-cases2)
     (parameterize ([metafunction-pict-style 'left-right/beside-side-conditions]
                    [where-make-prefix-pict
                     (λ ()
                       (text " if " (default-style)))])
       (htl-append 30
                   (vl-append
                    20
                    (render-metafunction unpair)
                    (render-metafunction sum-up-to))
                   (render-metafunction size)))))))

(define (unfair-rule)
  (w/rewriters
   (w/fonts
    (render-judgment-form @*))))

(define (some-rules linebreaking)
  (apply
   vc-append
   20
   (for/list ([line (in-list linebreaking)])
     (apply 
      hb-append
      25
      (for/list ([name (in-list line)])
        (parameterize ([judgment-form-cases (list name)])
          (render-judgment-form @)))))))

(define-syntax-rule 
  (sr e)
  (sr/proc (λ () (render-term L e))))
(define (sr/proc t) 
  (parameterize ([default-font-size 11])
    (w/fonts
     (w/rewriters
      (t)))))
(define (mf-name mf)
  (w/fonts
   ((current-text) mf (metafunction-style) (metafunction-font-size))))

(module+ main 
  (define sf (semantics-figure))
  sf
  (pict-width sf)
  (unfair-rule))