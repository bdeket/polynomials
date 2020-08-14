#lang typed/racket/base

(provide (struct-out iteration-result)
         print-iteration-result
         Iteration-Result
         Itermsg
         EndFct)

(define-type Itermsg
  (U 'done
     'max-iterations
     'local-extremum
     'invalid-region
     'algorithm-stoped))
(struct (A) iteration-result
  ([result : A]
   [endmsg : Itermsg]
   [iterations : Integer]
   [values : (Listof (List A A))]))
(define #:forall (A) (print-iteration-result [r : (iteration-result A)])
  (case (iteration-result-endmsg r)
    [(done)
     (printf "result: ~a\n" (iteration-result-result r))
     (printf "finished succesfully in ~a iterations\n" (iteration-result-iterations r))]
    [else
     (printf "did not finish (~a - ~a)\n" (iteration-result-endmsg r)(iteration-result-iterations r))
     ])
  (printf "last ~a steps:\n" (min 5 (length (iteration-result-values r))))
  (for ([i (in-list (iteration-result-values r))]
        [j (in-range 5)])
    (printf "  ~a\n" i)))
(define-type Iteration-Result iteration-result)
(define-type EndFct (All (A) (-> (Listof (List A A)) (Option Itermsg))))