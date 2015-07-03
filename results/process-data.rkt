#lang racket/base
#|

This script reads in the data from the files in the
given data and the writes out the results of calling
'process-data' on those files, via the main module

It also exports a function for reading the data from
a directory that checks to make sure the data isn't out of date

|#

(require redex/benchmark/private/graph-data
         racket/runtime-path
         racket/path)

(define-runtime-path directory "all")

(module+ main
  (require racket/cmdline racket/pretty)
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
    
    (call-with-output-file (format "~a.process-rate" directory)
      (λ (port)
        (pretty-write (fetch-rate) port))
      #:exists 'truncate)))

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

(provide read-data-for-directory read-rate-for-directory)
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
