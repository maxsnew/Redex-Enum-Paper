(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(start 2015-06-30T21:13:50 (#:model "rvm-4" #:type grammar))
(rvm-expected-exception 2015-06-30T23:32:17 (#:exn-message "heap-ref: (heap-ref #t ((x1 ((clos 0 () x))))) is not in my domain" #:expression (let-rec () (seq (let-rec () (lam () () #t)) (let-one #t (branch #f (boxenv 0 (quote R)) (loc-box 0)))))))
(counterexample 2015-06-30T23:32:17 (#:model "rvm-4" #:type grammar #:counterexample (let-rec () (seq (let-rec () (lam () () #t)) (let-one #t (branch #f (boxenv 0 (quote R)) (loc-box 0))))) #:iterations 1767641 #:time 8313203))
(new-average 2015-06-30T23:32:17 (#:model "rvm-4" #:type grammar #:average 8313203.0 #:stderr +nan.0))
(rvm-expected-exception 2015-06-30T23:48:50 (#:exn-message "heap-ref: (heap-ref 0 ()) is not in my domain" #:expression (let-one 0 (branch #f (boxenv 0 (lam () () 0)) (let-void-box 0 (loc-box-clr 0))))))
(counterexample 2015-06-30T23:48:50 (#:model "rvm-4" #:type grammar #:counterexample (let-one 0 (branch #f (boxenv 0 (lam () () 0)) (let-void-box 0 (loc-box-clr 0)))) #:iterations 2001319 #:time 9304201))
(new-average 2015-06-30T23:48:50 (#:model "rvm-4" #:type grammar #:average 9304201.0 #:stderr +nan.0))
(rvm-expected-exception 2015-07-01T03:09:17 (#:exn-message "heap-ref: (heap-ref (clos x7) ((x8 ((clos 0 () x3))) (x7 ((clos 0 () x) (clos 0 () x1) (clos 0 () x2))) (x4 undefined) (x5 undefined) (x6 undefined))) is not in my domain" #:expression (seq (let-one (let-void-box 3 (case-lam (lam () () void) (lam () () void) (lam () () #t))) (seq (branch (loc 0) 4 (boxenv 0 void)) (lam () () #t) (loc-box-clr 0))) (let-void 0 void))))
(counterexample 2015-07-01T03:09:17 (#:model "rvm-4" #:type grammar #:counterexample (seq (let-one (let-void-box 3 (case-lam (lam () () void) (lam () () void) (lam () () #t))) (seq (branch (loc 0) 4 (boxenv 0 void)) (lam () () #t) (loc-box-clr 0))) (let-void 0 void)) #:iterations 4591478 #:time 21340378))
(new-average 2015-07-01T03:09:17 (#:model "rvm-4" #:type grammar #:average 21340377.0 #:stderr +nan.0))
(rvm-expected-exception 2015-07-01T03:16:43 (#:exn-message "heap-ref: (heap-ref 0 ()) is not in my domain" #:expression (seq (let-one 0 (branch #f (boxenv 0 (application (loc-box-clr 0))) (loc-box-clr 0))) (quote g))))
(counterexample 2015-07-01T03:16:43 (#:model "rvm-4" #:type grammar #:counterexample (seq (let-one 0 (branch #f (boxenv 0 (application (loc-box-clr 0))) (loc-box-clr 0))) (quote g)) #:iterations 2723691 #:time 13467408))
(new-average 2015-07-01T03:16:43 (#:model "rvm-4" #:type grammar #:average 10890305.5 #:stderr 2577102.5))
(rvm-expected-exception 2015-07-01T03:41:57 (#:exn-message "heap-ref: (heap-ref (clos x1) ((x1 ((clos 0 () x))))) is not in my domain" #:expression (let-void-box 0 (let-one (lam () () (quote Q)) (branch #f (boxenv 0 (loc-box 0)) (loc-box-noclr 0))))))
(counterexample 2015-07-01T03:41:57 (#:model "rvm-4" #:type grammar #:counterexample (let-void-box 0 (let-one (lam () () (quote Q)) (branch #f (boxenv 0 (loc-box 0)) (loc-box-noclr 0)))) #:iterations 325699 #:time 1515385))
(new-average 2015-07-01T03:41:57 (#:model "rvm-4" #:type grammar #:average 7765332.0 #:stderr 3461109.42823314))
(rvm-expected-exception 2015-07-01T04:26:06 (#:exn-message "heap-ref: (heap-ref (clos x1) ((x1 ((clos 0 () x))))) is not in my domain" #:expression (let-void 1 (branch (install-value 0 (lam () () (quote S)) #f) (application (let-void-box 0 (boxenv 0 (loc-box-noclr 0)))) (loc-box-clr 0)))))
(counterexample 2015-07-01T04:26:06 (#:model "rvm-4" #:type grammar #:counterexample (let-void 1 (branch (install-value 0 (lam () () (quote S)) #f) (application (let-void-box 0 (boxenv 0 (loc-box-noclr 0)))) (loc-box-clr 0))) #:iterations 517860 #:time 2651220))
(new-average 2015-07-01T04:26:06 (#:model "rvm-4" #:type grammar #:average 6486804.0 #:stderr 2761208.627374282))
(rvm-expected-exception 2015-07-01T05:25:58 (#:exn-message "heap-ref: (heap-ref (clos x) ((x2 undefined) (x ((clos 1 () x1))))) is not in my domain" #:expression (let-one (proc-const (val) 3) (branch (branch (quote x) (let-void-box 1 (seq (loc-clr 0) void)) (let-void 0 (boxenv 0 (quote t)))) (loc-box 0) (loc-box-clr 0)))))
(counterexample 2015-07-01T05:25:58 (#:model "rvm-4" #:type grammar #:counterexample (let-one (proc-const (val) 3) (branch (branch (quote x) (let-void-box 1 (seq (loc-clr 0) void)) (let-void 0 (boxenv 0 (quote t)))) (loc-box 0) (loc-box-clr 0))) #:iterations 6174466 #:time 29538614))
(new-average 2015-07-01T05:25:58 (#:model "rvm-4" #:type grammar #:average 29538613.0 #:stderr +nan.0))
(rvm-expected-exception 2015-07-01T09:57:36 (#:exn-message "heap-set: (heap-set void void ((x4 ((clos 0 () x))) (x2 ((clos 0 () x3))))) is not in my domain" #:expression (let-one void (install-value-box 0 (branch (lam () () #t) (loc-noclr 0) (boxenv 0 (case-lam))) (branch (branch (case-lam) (quote K) (lam () () #f)) (loc-box-noclr 0) (install-value-box 0 (loc-box 0) (proc-const () 0)))))))
(counterexample 2015-07-01T09:57:36 (#:model "rvm-4" #:type grammar #:counterexample (let-one void (install-value-box 0 (branch (lam () () #t) (loc-noclr 0) (boxenv 0 (case-lam))) (branch (branch (case-lam) (quote K) (lam () () #f)) (loc-box-noclr 0) (install-value-box 0 (loc-box 0) (proc-const () 0))))) #:iterations 7900336 #:time 36545672))
(new-average 2015-07-01T09:57:36 (#:model "rvm-4" #:type grammar #:average 22924936.5 #:stderr 13620735.499999998))
(rvm-expected-exception 2015-07-01T10:32:30 (#:exn-message "heap-ref: (heap-ref (clos x3) ((x3 ((clos 1 () x))) (x1 ((clos 0 () x2))))) is not in my domain" #:expression (let-one (lam (val) () (application (proc-const () void))) (branch #f (branch (boxenv 0 (loc-box 0)) (install-value-box 0 (let-void-box 1 0) (loc-box 0)) (loc-box 0)) (let-void-box 0 (loc-box 0))))))
(counterexample 2015-07-01T10:32:30 (#:model "rvm-4" #:type grammar #:counterexample (let-one (lam (val) () (application (proc-const () void))) (branch #f (branch (boxenv 0 (loc-box 0)) (install-value-box 0 (let-void-box 1 0) (loc-box 0)) (loc-box 0)) (let-void-box 0 (loc-box 0)))) #:iterations 4719835 #:time 21996851))
(new-average 2015-07-01T10:32:30 (#:model "rvm-4" #:type grammar #:average 9588813.4 #:stderr 3767894.1290885624))
(rvm-expected-exception 2015-07-01T13:26:10 (#:exn-message "heap-ref: (heap-ref #f ()) is not in my domain" #:expression (seq (let-one #f (branch (loc 0) (boxenv 0 (loc-noclr 0)) (loc-box-noclr 0))) (let-rec () (application 3)))))
(counterexample 2015-07-01T13:26:10 (#:model "rvm-4" #:type grammar #:counterexample (seq (let-one #f (branch (loc 0) (boxenv 0 (loc-noclr 0)) (loc-box-noclr 0))) (let-rec () (application 3))) #:iterations 6079190 #:time 28826305))
(new-average 2015-07-01T13:26:10 (#:model "rvm-4" #:type grammar #:average 29182459.0 #:stderr 356154.0))
(rvm-expected-exception 2015-07-01T13:55:27 (#:exn-message "heap-ref: (heap-ref #f ((x1 ()))) is not in my domain" #:expression (seq (let-one #f (seq (branch (case-lam) (quote U) (boxenv 0 (loc-box 0))) (loc-box-noclr 0) (loc-noclr 0))) (lam (val val val) () (loc 1)))))
(counterexample 2015-07-01T13:55:27 (#:model "rvm-4" #:type grammar #:counterexample (seq (let-one #f (seq (branch (case-lam) (quote U) (boxenv 0 (loc-box 0))) (loc-box-noclr 0) (loc-noclr 0))) (lam (val val val) () (loc 1))) #:iterations 12648088 #:time 60126328))
(new-average 2015-07-01T13:55:27 (#:model "rvm-4" #:type grammar #:average 60126328.0 #:stderr +nan.0))
(rvm-expected-exception 2015-07-01T14:09:14 (#:exn-message "heap-ref: (heap-ref (clos x) ((x ((clos 0 () x1))))) is not in my domain" #:expression (seq (let-one (proc-const () #f) (branch (application (loc 0)) (boxenv 0 (loc-box-noclr 0)) (let-void-box 0 (loc-box 0)))) 1)))
(counterexample 2015-07-01T14:09:14 (#:model "rvm-4" #:type grammar #:counterexample (seq (let-one (proc-const () #f) (branch (application (loc 0)) (boxenv 0 (loc-box-noclr 0)) (let-void-box 0 (loc-box 0)))) 1) #:iterations 13062481 #:time 60960740))
(new-average 2015-07-01T14:09:14 (#:model "rvm-4" #:type grammar #:average 60960740.0 #:stderr +nan.0))
(rvm-expected-exception 2015-07-01T15:05:14 (#:exn-message "heap-ref: (heap-ref 4 ((x2 undefined) (x ((clos 0 () x1))))) is not in my domain" #:expression (branch (let-void-box 1 void) (let-one 4 (branch #f (boxenv 0 (proc-const () #t)) (let-rec () (loc-box-clr 0)))) void)))
(counterexample 2015-07-01T15:05:14 (#:model "rvm-4" #:type grammar #:counterexample (branch (let-void-box 1 void) (let-one 4 (branch #f (boxenv 0 (proc-const () #t)) (let-rec () (loc-box-clr 0)))) void) #:iterations 3392140 #:time 16370621))
(new-average 2015-07-01T15:05:14 (#:model "rvm-4" #:type grammar #:average 10719114.666666668 #:stderr 3277539.4834298557))
(rvm-expected-exception 2015-07-01T15:50:44 (#:exn-message "heap-ref: (heap-ref (quote q) ((x2 #t) (x ((clos 0 () x1))))) is not in my domain" #:expression (seq 0 void void (let-one #t (boxenv 0 (proc-const () (let-void-box 0 (quote indirect))))) (let-one (quote q) (application (branch #f (boxenv 0 (loc-box 0)) (loc-box-noclr 0)))) (let-void-box 0 (quote j)) 0)))
(counterexample 2015-07-01T15:50:44 (#:model "rvm-4" #:type grammar #:counterexample (seq 0 void void (let-one #t (boxenv 0 (proc-const () (let-void-box 0 (quote indirect))))) (let-one (quote q) (application (branch #f (boxenv 0 (loc-box 0)) (loc-box-noclr 0)))) (let-void-box 0 (quote j)) 0) #:iterations 1881464 #:time 8679920))
(new-average 2015-07-01T15:50:44 (#:model "rvm-4" #:type grammar #:average 22348279.333333332 #:stderr 6837272.38062461))
(rvm-expected-exception 2015-07-01T16:11:34 (#:exn-message "heap-ref: (heap-ref (clos x) ((x3 0) (x2 undefined) (x ((clos 0 () x1))))) is not in my domain" #:expression (let-void-box 1 (let-one (proc-const () 1) (let-one (branch (loc-box 2) 0 (boxenv 1 (quote J))) (boxenv 0 (loc-box 1)))))))
(counterexample 2015-07-01T16:11:34 (#:model "rvm-4" #:type grammar #:counterexample (let-void-box 1 (let-one (proc-const () 1) (let-one (branch (loc-box 2) 0 (boxenv 1 (quote J))) (boxenv 0 (loc-box 1))))) #:iterations 10157455 #:time 46962786))
(new-average 2015-07-01T16:11:34 (#:model "rvm-4" #:type grammar #:average 34151581.5 #:stderr 12811204.499999998))
(rvm-expected-exception 2015-07-01T16:25:43 (#:exn-message "heap-ref: (heap-ref (quote uJ) ((x ((clos 4 () x1))))) is not in my domain" #:expression (let-void 0 (let-one (let-void-box 0 (quote uJ)) (seq #f (branch (loc 0) (loc 0) (boxenv 0 1)) (let-void-box 0 (loc-box 0)) (proc-const (val val val val) (loc-noclr 0)))))))
(counterexample 2015-07-01T16:25:43 (#:model "rvm-4" #:type grammar #:counterexample (let-void 0 (let-one (let-void-box 0 (quote uJ)) (seq #f (branch (loc 0) (loc 0) (boxenv 0 1)) (let-void-box 0 (loc-box 0)) (proc-const (val val val val) (loc-noclr 0))))) #:iterations 4992945 #:time 23294390))
(new-average 2015-07-01T16:25:43 (#:model "rvm-4" #:type grammar #:average 23048087.666666668 #:stderr 7864899.537195085))
(rvm-expected-exception 2015-07-01T16:47:59 (#:exn-message "heap-ref: (heap-ref #f ((x1 ()) (x ()))) is not in my domain" #:expression (let-one #f (branch (branch (let-void 2 (case-lam)) (seq (seq (loc-noclr 0) 4) (case-lam)) (boxenv 0 (case-lam))) (loc-box 0) (loc-box-clr 0)))))
(counterexample 2015-07-01T16:47:59 (#:model "rvm-4" #:type grammar #:counterexample (let-one #f (branch (branch (let-void 2 (case-lam)) (seq (seq (loc-noclr 0) 4) (case-lam)) (boxenv 0 (case-lam))) (loc-box 0) (loc-box-clr 0))) #:iterations 708584 #:time 3436170))
(new-average 2015-07-01T16:47:59 (#:model "rvm-4" #:type grammar #:average 17620252.0 #:stderr 6762276.929272652))
(rvm-expected-exception 2015-07-01T18:51:24 (#:exn-message "heap-ref: (heap-ref void ()) is not in my domain" #:expression (branch (let-rec () (let-void-box 0 (let-void-box 0 void))) (let-one void (branch #f (boxenv 0 (loc-box-clr 0)) (loc-box-noclr 0))) #t)))
(counterexample 2015-07-01T18:51:24 (#:model "rvm-4" #:type grammar #:counterexample (branch (let-rec () (let-void-box 0 (let-void-box 0 void))) (let-one void (branch #f (boxenv 0 (loc-box-clr 0)) (loc-box-noclr 0))) #t) #:iterations 16068308 #:time 77892166))
(new-average 2015-07-01T18:51:24 (#:model "rvm-4" #:type grammar #:average 77892165.0 #:stderr +nan.0))
(finished 2015-07-01T21:13:02 (#:model "rvm-4" #:type grammar #:time-ms 86400003 #:attempts 18447688 #:num-counterexamples 1 #:rate-terms/s 213.5148999936956 #:attempts/cexp 18447688.0))
(finished 2015-07-01T21:13:05 (#:model "rvm-4" #:type grammar #:time-ms 86400245 #:attempts 18589033 #:num-counterexamples 2 #:rate-terms/s 215.15023481704247 #:attempts/cexp 9294516.5))
(finished 2015-07-01T21:13:08 (#:model "rvm-4" #:type grammar #:time-ms 86400002 #:attempts 18236672 #:num-counterexamples 6 #:rate-terms/s 211.07258770665305 #:attempts/cexp 3039445.3333333335))
(finished 2015-07-01T21:13:09 (#:model "rvm-4" #:type grammar #:time-ms 86400002 #:attempts 17825561 #:num-counterexamples 1 #:rate-terms/s 206.3143586501306 #:attempts/cexp 17825561.0))
(finished 2015-07-01T21:13:09 (#:model "rvm-4" #:type grammar #:time-ms 86400001 #:attempts 18182686 #:num-counterexamples 4 #:rate-terms/s 210.44775219389174 #:attempts/cexp 4545671.5))
(finished 2015-07-01T21:13:09 (#:model "rvm-4" #:type grammar #:time-ms 86400002 #:attempts 18131097 #:num-counterexamples 1 #:rate-terms/s 209.85065486456818 #:attempts/cexp 18131097.0))
(finished 2015-07-01T21:13:14 (#:model "rvm-4" #:type grammar #:time-ms 86400001 #:attempts 18565575 #:num-counterexamples 3 #:rate-terms/s 214.8793377907484 #:attempts/cexp 6188525.0))
(finished 2015-07-01T21:13:16 (#:model "rvm-4" #:type grammar #:time-ms 86400001 #:attempts 18609502 #:num-counterexamples 0 #:rate-terms/s 215.38775213671582 #:attempts/cexp N/A))