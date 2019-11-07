#lang typed/racket/base

#| TODO:
¿rename to field, this is (I think) closer to what this structure captures...?

expectations: (to be written in the doc.)

addition is assosiative: -> if not: everything is evaluated left to right
zero is neutral for addition: -> if not: zero is added to poly+, poly* and a few others
addition is commutative: -> if not: no order is guaranteed in the poly coefficients,
                                    especially for sparse coefficients, the complete order
                                    can change with just one extra term added

multiplication is assosiative: -> if not: exponents are not calculated the right way
                                          everything is evaluated left to right
multiplication is distributive w.r.t. addition: if not: poly-scale, poly* and poly-substitute are wrong
multiplication is commutative: -> if not: multiplication and substitution are not calculated the right way
                                         (a x y)*(b z x) => (a b x² y z) instead of (a x y b z x)
                                         ie: coefficients are grouped together in order and variables are sorted based on first appearance
                                         if I understand it right, this means implementation is ok for poly structures, but not for poly functions

- and / are defined functions: if not poly- and (poly/s & poly/p-QR) respectively will not work



|#

(provide make-algebra
         C-algebra
         algebra-->t algebra-t=
         algebra-t+ algebra-t- algebra-t* algebra-t/
         algebra-zero algebra-one
         Algebra)
;***********************************************************************************************************************
;* Algebra                                                                                                             *
;***********************************************************************************************************************
(struct (TheType) algebra
  ([->t  : (Any -> TheType)]
   [t=   : (TheType TheType -> Boolean)]
   [t+   : (TheType TheType -> TheType)]
   [t*   : (TheType TheType -> TheType)]
   [t-   : (TheType TheType -> TheType)]
   [t/   : (TheType TheType -> TheType)]
   [zero : TheType]
   [one  : TheType])
  #:type-name Algebra)
;an (Algebra Integer) can not be an (Algebra Number) because
;Integer+ can not accept 4.5 (for example)
;an (Algebra Integer) can not be an (Algebra Integer) because
;Number/ (on integers) can produce 4.5
;it still would be nice to be able to check at compile time if
;something is an (Algebra TheType) (for any TheType ;) )

(: make-algebra (All (TheType)
                     (case-> (->* [(TheType TheType -> TheType)
                                   (TheType TheType -> TheType)]
                                  [(TheType TheType -> TheType)
                                   (TheType TheType -> TheType)
                                   #:->t (Option (Any -> TheType))
                                   #:i->t (Option (Integer -> TheType))
                                   #:Zero (Option TheType)
                                   #:One (Option TheType)
                                   #:equal? (TheType TheType -> Boolean)]
                                  (Algebra TheType)))))
(define (make-algebra t+ t*
                      [t- (λ (x y)(error "algebra: -(difference) not implemented"))]
                      [t/ (λ (x y)(error "algebra: /(division) not implemented"))]
                      #:->t [->t #f]
                      #:i->t [i->t #f]
                      #:Zero [zero #f]
                      #:One [one  #f]
                      #:equal? [t=   equal?])
  (define-values (->t* Zero* One*)
    (cond
      [->t (values ->t (or zero (->t 0))(or one (->t 1)))]
      [i->t (values (λ (x)
                      (cond
                        [(exact-integer? x) (i->t x)]
                        [else (error (format "algebra->t: Unable to convert ~a to TheType of the algebra" x))]))
                    (or zero (i->t 0))(or one (i->t 1)))]
      [(and zero one)
       (values (λ (x)
                 (cond
                   [(integer? x)
                    (define +/- (if (< x 0) t- t+))
                    (for/fold : TheType ([s zero])([i (in-range (abs x))])(+/- s one))]
                   [else (raise-argument-error 'algebra "Unable to convert to thetype" x)]))
               zero one)]
      [else (raise-argument-error 'make-algebra "Either ->t or Zero and One need to be defined" (list ->t zero one))]))
  (algebra ->t* t= t+ t* t- t/ Zero* One*))

(define C-algebra
    ((inst make-algebra Number)
     + * - /
     #:equal? =
     #:->t (λ (x) (if (number? x) x
                      (error "C-algebra: don't know how to convert to number:" x)))))