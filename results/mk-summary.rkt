#lang racket
(require "process-data.rkt"
         racket/runtime-path)
(define-values (all-names data-stats name-avgs max-non-f-value-from-list-ref-d2)
  (apply values (read-data-for-directory)))

(define-runtime-path summary.rktd "summary.rktd")
(call-with-output-file summary.rktd
  (λ (port)
    (fprintf port ";; This is the data from the evaluation. Each line is of the form:\n")
    (fprintf port ";;   (bug-name generator average-time-in-seconds)\n")
    (fprintf port ";; where the bug-names match the x axis, `enum' means\n")
    (fprintf port ";; in order enumeration, `ordered' means random selection\n")
    (fprintf port ";; from the enumeration, `grammar' means the ad hoc random\n")
    (fprintf port ";; generator. If there is no prefix, then the enumerator is\n")
    (fprintf port ";; fair and otherwise it is unfair as indicated.\n\n")
    (for ([data-stat (in-list data-stats)])
      (define bug (list-ref data-stat 0))
      (define gen-method (list-ref data-stat 1))
      (define time-taken (list-ref data-stat 2))
      (fprintf port "~s\n" (list bug gen-method time-taken))))
  #:exists 'truncate)

