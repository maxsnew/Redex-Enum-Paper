#lang racket/base
#|

The main module in this script reads in the data from the
all/ directory and creates the summaries in all.process-*

It also exports functions for reading the data from the
summaries that checks to make sure the data isn't out of date.

|#

(require redex/benchmark/private/graph-data
         racket/runtime-path
         racket/path
         racket/set
         racket/system)

(provide read-data-for-directory read-rate-for-directory
         type-name->description
         type-name->generic-description)

(define (type-name->description name)
  (case name
    [(grammar) "Ad Hoc Random Generation"]
    [(ordered) "In-Order Enumeration, Fair"]
    [(ordered-mildly-unfair) "In-Order Enumeration, Mildly Unfair"]
    [(ordered-brutally-unfair) "In-Order Enumeration, Brutally Unfair"]
    [(enum) "Uniform Random Selection, Fair"]
    [(enum-mildly-unfair) "Uniform Random Selection, Mildly Unfair"]
    [(enum-brutally-unfair) "Uniform Random Selection, Brutally Unfair"]))

(define (type-name->generic-description name)
  (case name
    [(grammar) "Ad Hoc Random Generation"]
    [(ordered) "In-Order Enumeration"]
    [(enum) "Uniform Random Selection"]
    [else (error 'type-name->generic-description
                 "expected either 'grammar 'ordered or 'enum, got ~s"
                 name)]))


(define-runtime-path directory "all")
(define-runtime-path dominates.dot "dominates.dot")
(define-runtime-path dominates.pdf "dominates.pdf")

(define (build-dominates-pdf)
  (define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
    (apply values (read-data-for-directory)))

  ;; info : [generator -o> (setof bug)]
  (define info (make-hash))

  (define gen-methods (set))
  
  (for ([data-stat (in-list data-stats)])
    (define bug (list-ref data-stat 0))
    (define gen-method (list-ref data-stat 1))
    (set! gen-methods (set-add gen-methods gen-method))
    (define time-taken (list-ref data-stat 2))
    (hash-set! info gen-method (set-add (hash-ref info gen-method set) bug)))

  (define edges '())
  (for ([gen-method1 (in-set gen-methods)])
    (for ([gen-method2 (in-set gen-methods)])
      (when (proper-subset? (hash-ref info gen-method1)
                            (hash-ref info gen-method2))
        (set! edges (cons (cons gen-method2 gen-method1) edges)))))

  (set! edges (sort edges string<? #:key (λ (x) (format "~s" x))))

  (define (neighbors node)
    (for/list ([n (in-set gen-methods)]
               #:when (member (cons node n) edges))
      n))
  
  (define (longest-path start end)
    (cond
      [(equal? start end) 0]
      [else
       (define s-ns (neighbors start))
       (define path-lengths
         (for/list ([s-n (in-list s-ns)])
           (longest-path s-n end)))
       (define connected-lengths (filter values path-lengths))
       (cond
         [(null? connected-lengths) #f]
         [else (+ (apply max connected-lengths) 1)])]))
  
  (define (is-transitive? edge)
    (> (longest-path (car edge) (cdr edge)) 1))
  
  (define nt-edges
    (for/list ([edge (in-list edges)]
               #:unless (is-transitive? edge))
      edge))

  (call-with-output-file dominates.dot
    (λ (port)
      (fprintf port "digraph {\n")
      (fprintf port " margin=0\n")
      (for ([gen-method (in-set gen-methods)])
        (define name (regexp-split #rx", " (type-name->description gen-method)))
        (define formatted-name
          (if (null? (cdr name))
              (car name)
              (format "~a\\n~a"
                      (list-ref name 1)
                      (list-ref name 0))))
        (fprintf port "  \"~a\" [label=\"~a\", shape=box]\n"
                 gen-method
                 formatted-name))
      (for ([nt-edge (in-list nt-edges)])
        (fprintf port "  \"~a\" -> \"~a\"\n"
                 (car nt-edge) (cdr nt-edge)))
      (fprintf port "}\n"))
    #:exists 'truncate)

  (call-with-output-file dominates.pdf
    (λ (port)
      (parameterize ([current-output-port port]
                     [current-input-port (open-input-string "")])
        (unless (system* "/usr/local/bin/dot"
                         "-Tpdf"
                         (format "~a" dominates.dot))
          (error 'process-data.rkt "call to dot failed"))))
    #:exists 'truncate))

(module+ main
  (require racket/cmdline racket/pretty)

  (define skip-all-process? #f)

  (command-line
   #:once-each
   [("--skip-process") "generate only dominates.pdf" (set! skip-all-process? #t)])
  
  (unless skip-all-process?
    (printf "building all.process-data\n")
    
    (define all-names (extract-names/log-directory directory))
    (define data (extract-data/log-directory directory))
    
    (define-values (data-stats name-avgs)
      (process-data
       data
       all-names))
    (define max-non-f-value-from-list-ref-d2
      (apply max (filter values (map (λ (d) (list-ref d 2)) data))))
    
    (parameterize ([current-directory (simple-form-path (build-path directory 'up))])
      (call-with-output-file (format "~a.process-data" directory)
        (λ (port) 
          (pretty-write (list all-names data-stats name-avgs max-non-f-value-from-list-ref-d2) port)
          (newline port))
        #:exists 'truncate)
      
      (printf "building all.process-rate\n")
      (call-with-output-file (format "~a.process-rate" directory)
        (λ (port)
          (pretty-write (fetch-rate) port))
        #:exists 'truncate)))

  (printf "building dominates.pdf\n")
  (build-dominates-pdf)

  (printf "done.\n"))

(define (check-mod-and-read suffix)
  (define data-file (format "~a.process-~a" directory suffix))
  (unless (file-exists? data-file)
    (error 'read-data-for-directory "expected file ~a to exist" data-file))
  (unless (directory-exists? directory)
    (error 'read-data-for-directory "expected directory ~a to exist" directory))
  (define data-file-mod (file-or-directory-modify-seconds data-file))
  (for ([file (in-directory directory)])
    (when (file-exists? file)
      (unless (<= (file-or-directory-modify-seconds file) data-file-mod)
        (error 'read-data-for-directory
               "file ~a is newer than ~a, so ~a needs to be rebuilt"
               file data-file data-file))))
  (call-with-input-file data-file read))

(define (read-data-for-directory) (check-mod-and-read "data"))
(define (read-rate-for-directory) (check-mod-and-read "rate"))

(define (fetch-rate)
  (for/list ([file (in-directory directory)])
    (call-with-input-file file
      (λ (port)
        (let loop ([previous-line #f])
          (define l (read port))
          (cond
            [(eof-object? l)
             (unless (and (pair? previous-line)
                          (equal? (car previous-line) 'finished))
               (error 'fetch-rate "problem, last line of ~a isn't finished, but: ~s"
                      file previous-line))
             (define data (list-ref previous-line 2))
             (define (lookup key)
               (let loop ([data data])
                 (cond
                   [(equal? (car data) key) (cadr data)]
                   [else (loop (cddr data))])))
             (list (lookup '#:model)
                   (lookup '#:type)
                   (lookup '#:rate-terms/s))]
            [else (loop l)]))))))
