(start 2015-06-17T12:09:23 (#:model "let-poly-4" #:type enum-mildly-unfair))
(counterexample 2015-06-17T21:58:32 (#:model "let-poly-4" #:type enum-mildly-unfair #:counterexample ((λ a (a a)) (cons cons)) #:iterations 2756989 #:time 35365285))
(new-average 2015-06-17T21:58:32 (#:model "let-poly-4" #:type enum-mildly-unfair #:average 35365284.0 #:stderr +nan.0))
(counterexample 2015-06-17T23:33:34 (#:model "let-poly-4" #:type enum-mildly-unfair #:counterexample ((λ a (a a)) (let ((b +)) b)) #:iterations 584140 #:time 5706136))
(new-average 2015-06-17T23:33:34 (#:model "let-poly-4" #:type enum-mildly-unfair #:average 20535710.0 #:stderr 14829573.999999998))
(counterexample 2015-06-18T04:08:25 (#:model "let-poly-4" #:type enum-mildly-unfair #:counterexample (let ((a ((λ a a) +))) (let ((b (a a))) new)) #:iterations 1709750 #:time 16504669))
(new-average 2015-06-18T04:08:25 (#:model "let-poly-4" #:type enum-mildly-unfair #:average 19192029.666666668 #:stderr 8666654.401325352))
(counterexample 2015-06-18T09:59:28 (#:model "let-poly-4" #:type enum-mildly-unfair #:counterexample ((λ a (a a)) (let ((c +)) cons)) #:iterations 2182629 #:time 21077853))
(new-average 2015-06-18T09:59:28 (#:model "let-poly-4" #:type enum-mildly-unfair #:average 19663485.5 #:stderr 6146358.259879591))
(finished 2015-06-18T12:08:28 (#:model "let-poly-4" #:type enum-mildly-unfair #:time-ms 86400003 #:attempts 8037283 #:num-counterexamples 4 #:rate-terms/s 93.02410556629263 #:attempts/cexp 2009320.75))
