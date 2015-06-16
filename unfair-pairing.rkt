#lang racket/base

(require parser-tools/lex
         parser-tools/cfg-parser
         parser-tools/yacc
         rackunit
         racket/set racket/contract)

(provide bad-max-x bad-max-y
         bad-howmany
         bad-nn->n-string)

(define bad-nn->n-string "\\lambda x. \\lambda y.\\ 2^y\\cdot{}(2x + 1) - 1")

(define-empty-tokens the-tokens
  (t:eof
   t:x t:y
   t:2 t:1
   t:+ t:- t:^ t:·
   t:λ t:dot
   t:open t:close))

(define lex-port
  (lexer
   [#\x (token-t:x)]
   [#\y (token-t:y)]
   [#\2 (token-t:2)]
   [#\1 (token-t:1)]
   [#\+ (token-t:+)]
   [#\- (token-t:-)]
   [#\^ (token-t:^)]
   ["\\cdot{}" (token-t:·)]
   ["\\lambda" (token-t:λ)]
   [#\. (token-t:dot)]
   [#\( (token-t:open)]
   [#\) (token-t:close)]
   [whitespace (lex-port input-port)]
   ["\\ " (lex-port input-port)]))

(define (lex str)
  (define p (open-input-string str))
  (λ ()
    (cond
      [(eof-object? (peek-char p))
       't:eof]
      [else
       (lex-port p)])))

(define (lex->list str)
  (define l (lex str))
  (let loop ()
    (define t (l))
    (cond
      [(equal? 't:eof t) '()]
      [else (cons t (loop))])))

(check-equal? (lex->list "1") (list (token-t:1)))
(check-equal? (lex->list "1 + 2") (list (token-t:1)
                                        (token-t:+)
                                        (token-t:2)))


(define formula-parser
  (parser
   (tokens the-tokens)
   (start exp)
   (end t:eof)
   (error (λ args (error 'formula-parser "~s" args)))
   (precs (left t:+ t:-))
   (grammar
    (exp ([lam-exp] $1))
    (add-exp ([add-exp t:+ mult-exp] `(+ ,$1 ,$3))
             ([add-exp t:- mult-exp] `(- ,$1 ,$3))
             ([mult-exp] $1))
    (mult-exp ([pow-exp t:· pow-exp] `(* ,$1 ,$3))
              ([pow-exp pow-exp] `(* ,$1 ,$2))
              ([pow-exp] $1))
    (pow-exp ([base-exp t:^ base-exp] `(expt ,$1 ,$3))
             ([base-exp] $1))
    (base-exp ([var] $1)
              ([t:1] 1)
              ([t:2] 2)
              ([t:open add-exp t:close] $2))
    
    (lam-exp ([t:λ vars lam-exp] `(λ ,$2 ,$3))
             ([add-exp] $1))
    (var ([t:x] 'x) ([t:y] 'y))
    (vars ([var vars] (cons $1 $2))
          ([var t:dot] (list $1))))))


(check-equal? (formula-parser (lex "x+y\\cdot{}2")) '(+ x (* y 2)))
(check-equal? (formula-parser (lex "x+y-2")) '(- (+ x y) 2))
(check-equal? (formula-parser (lex "x-y-2")) '(- (- x y) 2))

(define bad-nn->n
  (let ([curried
         (parameterize ([current-namespace (make-base-namespace)])
           (eval (formula-parser (lex bad-nn->n-string))))])
    (λ (x y) ((curried x) y))))

(define (bad-n->nn n)
  (define twos 0)
  (define leftover
    (let loop ([n (+ n 1)])
      (cond
        [(and (not (zero? n)) (even? n))
         (set! twos (+ twos 1))
         (loop (/ n 2))]
        [else n])))
  (values (/ (- leftover 1) 2) twos))

(for ([i (in-range 100000)])
  (define-values (x y) (bad-n->nn i))
  (define j (bad-nn->n x y))
  (unless (= i j)
    (error 'bad-bijection-fails "~s => ~s ~s => ~s"
           i x y j)))

(define bad-howmany 10000)
(define-values (bad-max-x bad-max-y)
  (for/fold ([max-x 0][max-y 0])
            ([i (in-range bad-howmany)])
    (define-values (x y) (bad-n->nn i))
    (values (max x max-x) (max y max-y))))

(define/contract (z_to_n n)
  (-> exact-nonnegative-integer?
      (set/c exact-nonnegative-integer?))
  (cond
    [(zero? n) (set)]
    [else (set-add (z_to_n (- n 1)) (- n 1))]))
(define (div2 n) (floor (/ n 2)))

(define (Trace_lt-unfair-pair n)
  (cond
    [(zero? n) (values (set) (set))]
    [else
     (define-values (x y) (bad-n->nn (- n 1)))
     (define-values (sx sy) (Trace_lt-unfair-pair (- n 1)))
     (values (set-add sx x)
             (set-add sy y))]))

(for ([n (in-range 0 100)])
  (define-values (explored-x explored-y) (Trace_lt-unfair-pair n))
  (define claimed-x (z_to_n (div2 (+ n 1))))
  (unless (equal? explored-x claimed-x)
    (error 'unfair-pairing.rkt "x ~a wrong: claimed ~s vs explored ~s\n"
           n claimed-x explored-x)))

(module+ main
  (require plot)
  (define x-ht (make-hash))
  (define y-ht (make-hash))
  (define (hash-inc! ht v) (hash-set! ht v (+ (hash-ref ht v 0) 1)))
  (define (to-lines ht)
    (sort
     (for/list ([(k v) (in-hash ht)])
       (vector k v))
     <
     #:key (λ (x) (vector-ref x 0))))
  (for ([i (in-range 1000)])
    (define-values (x y) (bad-n->nn i))
    (hash-inc! x-ht x)
    (hash-inc! y-ht y))
  (plot
   (list
    (lines (to-lines x-ht) #:color "red" #:label "x")
    (lines (to-lines y-ht) #:color "blue" #:label "y")))



  (define (find-equilibria n->nn)
    (define x-ht (make-hash))
    (define y-ht (make-hash))
    (define (hash-inc! ht n) (hash-set! ht n (+ 1 (hash-ref ht n 0))))
    (define (equilibria?) (equal? x-ht y-ht))
    (define limit 100000)
    (for ([i (in-range limit)])
      (define-values (x y) (n->nn i))
      (hash-inc! x-ht x)
      (hash-inc! y-ht y)
      (when (equilibria?)
        (printf "equilibria @ ~a:\n  x: ~s\n  y: ~s\n"
                i
                (sort (hash-map x-ht list) < #:key car)
                (sort (hash-map y-ht list) < #:key car))))
    (printf "stopped searching at ~a\n" limit))

  (find-equilibria bad-n->nn))
