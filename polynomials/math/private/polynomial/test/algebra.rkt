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
         I-algebra Q-algebra R-algebra C-algebra B-algebra
         (rename-out [algebra+*-->t algebra-->t]
                     [algebra+*-t= algebra-t=]
                     [algebra+*-t+ algebra-t+]
                     [algebra+*-t* algebra-t*]
                     [algebra+*--t- algebra-t-]
                     [algebra+*-zero algebra-zero]
                     [algebra+*-one algebra-one])
         algebra-t/
         Algebra Algebra+* Algebra+*-)
;***********************************************************************************************************************
;* Algebra                                                                                                             *
;***********************************************************************************************************************
(struct (A) algebra+*
  ([->t  : (Any -> A)]
   [t=   : (A A -> Boolean)]
   [t+   : (A A -> A)]
   [t*   : (A A -> A)]
   [zero : A]
   [one  : A])
  #:type-name Algebra+*)
(struct (A) algebra+*- algebra+*
  ([t-   : (A A -> A)])
  #:type-name Algebra+*-)
(struct (A) algebra algebra+*-
  ([t/   : (A A -> A)])
  #:type-name Algebra)
;an (Algebra Integer) can not be an (Algebra Number) because
;Integer+ can not accept 4.5 (for example)
;an (Algebra Number) can not be an (Algebra Integer) because
;Number/ (on integers) can produce 4.5
;it still would be nice to be able to check at compile time if
;something is an (Algebra A) (for any A ;) )

(define #:forall (A) (get-zero [->t : (Option (-> Any A))]
                               [i->t : (Option (-> Integer A))]
                               [zero : (Option A)][one : (Option A)]) : (Values (-> Any A) A A)
  (cond
    [->t (values ->t (or zero (->t 0))(or one (->t 1)))]
    [i->t (values (λ (x)
                    (cond
                      [(exact-integer? x) (i->t x)]
                      [else (error (format "algebra->t: Unable to convert ~a to the type of the algebra" x))]))
                  (or zero (i->t 0))(or one (i->t 1)))]
    [(and zero one)
     (values (λ (x) (cond [(equal? x 0) zero]
                          [(equal? x 1) one]
                          [else (raise-argument-error 'algebra "Unable to convert to the type" x)]))
             zero one)]
    [else (raise-argument-error 'make-algebra "Either ->t or Zero and One need to be defined" (list ->t zero one))]))
(: make-algebra+* (All (A) (->* [(A A -> A)
                                 (A A -> A)]
                                [ #:->t (Option (Any -> A))
                                  #:i->t (Option (Integer -> A))
                                  #:Zero (Option A)
                                  #:One (Option A)
                                  #:equal? (A A -> Boolean)]
                                (Algebra+* A))))
(define (make-algebra+* t+ t* #:->t [->t #f] #:i->t [i->t #f] #:Zero [zero #f] #:One [one #f] #:equal? [t= equal?])
  (define-values (->t* Zero* One*) (get-zero ->t i->t zero one))
  (algebra+* ->t* t= t+ t* Zero* One*))

(: make-algebra+*- (All (A) (->* [(A A -> A)
                                  (A A -> A)
                                  (A A -> A)]
                                [ #:->t (Option (Any -> A))
                                  #:i->t (Option (Integer -> A))
                                  #:Zero (Option A)
                                  #:One (Option A)
                                  #:equal? (A A -> Boolean)]
                                (Algebra+*- A))))
(define (make-algebra+*- t+ t* t- #:->t [->t #f] #:i->t [i->t #f] #:Zero [zero #f] #:One [one #f] #:equal? [t= equal?])
  (define-values (->t* Zero* One*) (get-zero ->t i->t zero one))
  (algebra+*- ->t* t= t+ t* Zero* One* t-))

(: make-algebra (All (A) (->* [(A A -> A)
                               (A A -> A)
                               (A A -> A)
                               (A A -> A)]
                              [ #:->t (Option (Any -> A))
                                #:i->t (Option (Integer -> A))
                                #:Zero (Option A)
                                #:One (Option A)
                                #:equal? (A A -> Boolean)]
                              (Algebra A))))
(define (make-algebra t+ t* t- t/ #:->t [->t #f] #:i->t [i->t #f] #:Zero [zero #f] #:One [one #f] #:equal? [t= equal?])
  (define-values (->t* Zero* One*) (get-zero ->t i->t zero one))
  (algebra ->t* t= t+ t* Zero* One* t- t/))


(define I-algebra
  ((inst make-algebra+*- Integer)
   (ann + (-> Integer Integer Integer))
   (ann * (-> Integer Integer Integer))
   (ann - (-> Integer Integer Integer))
   #:equal? =
   #:->t (λ (x) (cond
                  [(exact-integer? x) x]
                  [(integer? x) (floor (inexact->exact x))]
                  [else (error "I-algebra: don't know how to convert to Integer:" x)]))))

(define Q-algebra
    ((inst make-algebra Exact-Rational)
     + * - /
     #:equal? =
     #:->t (λ (x) (if (and (exact? x) (real? x)) x
                      (error "Q-algebra: don't know how to convert to Rational:" x)))))

(define R-algebra
    ((inst make-algebra Real)
     + * - /
     #:equal? =
     #:->t (λ (x) (if (real? x) x
                      (error "R-algebra: don't know how to convert to Real:" x)))))

(define C-algebra
    ((inst make-algebra Number)
     + * - /
     #:equal? =
     #:->t (λ (x) (if (number? x) x
                      (error "C-algebra: don't know how to convert to Number:" x)))))




(define B-algebra
  (let ()
    (define (⊕ [x : Boolean][y : Boolean]) (xor x y))
    (define (⊖ [x : Boolean][y : Boolean]) (xor x y))
    (define (⊗ [x : Boolean][y : Boolean]) (and x y))
    (define (⊘ [x : Boolean][y : Boolean]) (and x y))
    (define (xor [x : Boolean][y : Boolean]) (and (or x y)(not (and x y))))
  
    ((inst make-algebra Boolean)
     ⊕ ⊗ ⊖ ⊘
     #:->t (λ (x) (cond [(or (equal? x #f)(and (number? x)(= x 0))) #f][else #t])))))