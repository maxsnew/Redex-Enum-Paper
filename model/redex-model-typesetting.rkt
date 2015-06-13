#lang racket
(require redex
         pict
         "redex-model.rkt")

(provide semantics-figure sr)

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
         (hbl-append (d "‖") arg (d "‖"))]
        [`(sum-all ,e ,f)
         (maybe-add-parens
          needs-parens?
          (hbl-append (d "Σ x ∈ ") (loop #t e) (d ". ‖") (loop #t f) (d "(x)‖")))]
        [`(min ,ae1 ,ae2)
         (hbl-append (d "min(") (loop #f ae1) (d ",") (loop #f ae1) (d ")"))]
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
      [add? (hbl-append (t "(") p (t ")"))]
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
    (list "" enum " @ " n " = " v " | " T ""))
  
  (with-compound-rewriters
   (['@ @-rewrite]
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
       (list "∀ x ∈ " e ",  ‖" f "(x)‖ = ∞"))]
    ['fin?
     (λ (lws)
       (define e (list-ref lws 3))
       (define f (list-ref lws 4))
       (define @-rewritten
         (@-rewrite (list '_ '_ e
                          "n"
                          "v"
                          "T")))
       (list "∀ x ∈ " e ",  ‖" f "(x)‖ < ∞"))]
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
       (list "Σ x ∈ " e ". ‖" f "(x)‖"))]
    ['size
     (λ (lws)
       (list "‖" (list-ref lws 2) "‖"))]
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
       (list "sum_up_to(" (list-ref lws 2) ", " (list-ref lws 3) ", " (list-ref lws 4) ")"))]
    ['sum-up-to/render
     (λ (lws)
       (define f (list-ref lws 2))
       (define e (list-ref lws 3))
       (define n (list-ref lws 4))
       (list (d "Σ{‖") f (d "(v)‖ | ") e (d "@ i = v and i < ") n (d "}")))]
    ['Eval-enum (λ (lws) (list "" (list-ref lws 2) ""))]
    ['Eval-bij (λ (lws) (list "" (list-ref lws 2) ""))])
   (with-atomic-rewriter
    '∞ (λ () (d "∞"))
    (thunk))))

(define-syntax-rule (w/rewriters e) (w/rewriters/proc (λ () e)))

(define linebreaking-with-cases1
  '(("cons")
    ("trace")))

(define linebreaking-with-cases2
  '(("or alt l" "or alt r")
    ("or big l" "or big r")
    ("dep" "map" "below/e")
    ("ex<" "ex≥" "fix")))

(define (semantics-figure)
  (define helv-font "Helvetica")
  (define font-size 11)
  (parameterize ([label-font-size font-size]
                 [default-font-size font-size]
                 [metafunction-font-size font-size]
                 [metafunction-style helv-font]
                 [literal-style helv-font]
                 [grammar-style helv-font])
    (w/rewriters
     (vc-append
      20
      (ht-append 
       60
       (inset (frame (inset (render-language L #:nts '(e n+ v)) 4)) 4)
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
    (w/rewriters
     (t))))

(module+ main 
  (define sf (semantics-figure))
  sf
  (pict-width sf))
