#lang racket/base
#|

This script reads in the data from the files in the
given data and the writes out the results of calling
'process-data' on those files, via the main module

It also exports a function for reading the data from
a directory that checks to make sure the data isn't out of date

|#

(require redex/benchmark/private/graph-data
         racket/runtime-path)

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
  (call-with-output-file (format "~a.process-data" directory)
    (λ (port) 
      (pretty-write (list all-names data-stats name-avgs max-non-f-value-from-list-ref-d2) port)
      (newline port))
    #:exists 'truncate))

(provide read-data-for-directory)
(define (read-data-for-directory)
  (define data-file (format "~a.process-data" directory))
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
