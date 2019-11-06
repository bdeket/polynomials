#lang typed/racket/base

(provide (all-defined-out))
;***********************************************************************************************************************
;* Algebra                                                                                                             *
;***********************************************************************************************************************

(struct (TheType) algebra
  ([->t  : (Any -> TheType)]
   [t=   : (TheType TheType -> Boolean)]
   [t+   : (TheType TheType -> TheType)]
   [t-   : (TheType TheType -> TheType)]
   [t*   : (TheType TheType -> TheType)]
   [t/   : (TheType TheType -> TheType)]
   [tsum : ((Listof TheType) -> TheType)]
   [Zero : TheType]
   [One  : TheType])
  #:type-name Algebra)

(: make-algebra (All (TheType)
                     (case-> (->* [(TheType TheType -> TheType)
                                   (TheType TheType -> TheType)
                                   (TheType TheType -> TheType)
                                   (TheType TheType -> TheType)]
                                  [#:->t (Option (Any -> TheType))
                                   #:i->t (Option (Integer -> TheType))
                                   #:Zero (Option TheType)
                                   #:One (Option TheType)
                                   #:equal? (TheType TheType -> Boolean)
                                   #:sum (Option ((Listof TheType) -> TheType))]
                                  (Algebra TheType)))))
(define (make-algebra t+ t- t* t/
                      #:->t [->t #f]
                      #:i->t [i->t #f]
                      #:Zero [Zero #f]
                      #:One [One  #f]
                      #:equal? [t=   equal?]
                      #:sum [tsum #f])
  (define-values (->t* Zero* One*)
    (cond
      [->t (values ->t (or Zero (->t 0))(or One (->t 1)))]
      [i->t (values (λ (x)
                      (cond
                        [(exact-integer? x) (i->t x)]
                        [else (raise-argument-error 'algebra "Unable to convert to thetype" x)]))
                    (or Zero (i->t 0))(or One (i->t 1)))]
      [(and Zero One)
       (values (λ (x)
                 (cond
                   [(integer? x)
                    (define +/- (if (< x 0) t- t+))
                    (for/fold : TheType ([s Zero])([i (in-range (abs x))])(+/- s One))]
                   [else (raise-argument-error 'algebra "Unable to convert to thetype" x)]))
               Zero One)]
      [else (raise-argument-error 'make-algebra "Either ->t or Zero and One need to be defined" (list ->t Zero One))]))
  (define tsum* (or tsum (λ ([x : (Listof TheType)]) : TheType (for/fold ([s Zero*])([v (in-list x)])(t+ s v)))))
  (algebra ->t* t= t+ t- t* t/ tsum* Zero* One*))