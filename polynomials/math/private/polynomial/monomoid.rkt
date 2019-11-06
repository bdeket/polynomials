#lang typed/racket/base

(require racket/list)

(provide (all-defined-out))
;***********************************************************************************************************************
;* Monomoid                                                                                                            *
;***********************************************************************************************************************
(define-type Monomoid-Exponents (Vectorof Nonnegative-Integer))
(define-type Monomoid-Base (Vectorof Symbol))
(: monomoid (case-> (->* () #:rest Nonnegative-Integer Monomoid-Exponents)
             (->* () #:rest Symbol Monomoid-Base)))
(define (monomoid . x) (list->vector x))
(define (monomoid-base->zero-exponent [b : Monomoid-Base]): Monomoid-Exponents (make-vector (monomoid-length b) 0))

(: list->monomoid (case-> (-> (Listof Nonnegative-Integer) Monomoid-Exponents)(-> (Listof Symbol) Monomoid-Base)))
(define (list->monomoid l) (list->vector l))

(: monomoid->list (case-> (-> Monomoid-Exponents (Listof Nonnegative-Integer))(-> Monomoid-Base (Listof Symbol))))
(define (monomoid->list v) (vector->list v))

(define (monomoid-length [x : (U Monomoid-Exponents Monomoid-Base)]) : Nonnegative-Integer (vector-length x))

(: monomoid-ref (case-> (-> Monomoid-Exponents Nonnegative-Integer Nonnegative-Integer)(-> Monomoid-Base Nonnegative-Integer Symbol)))
(define (monomoid-ref x i) (vector-ref x i))

(: monomoid-first (case-> (-> Monomoid-Exponents Nonnegative-Integer)(-> Monomoid-Base Symbol)))
(define (monomoid-first x)(monomoid-ref x 0))

(define (monomoid-has? [vars : Monomoid-Base][var : Symbol]) : (Option Nonnegative-Integer)
  (for/or ([v (in-vector vars)]
           [i : Nonnegative-Integer (in-naturals)])
    (and (equal? var v)i)))

(define (monomoid-combine [b1 : Monomoid-Base][b2 : Monomoid-Base])
  : (Values Monomoid-Base
            (-> Monomoid-Exponents Monomoid-Exponents)
            (-> Monomoid-Exponents Monomoid-Exponents))
  (define vars (list->monomoid (remove-duplicates (append (monomoid->list b1)(monomoid->list b2)))))
  (define vars-len (monomoid-length vars))
  (define dif (make-list (- vars-len (monomoid-length b1)) 0))
  (define k-map : (HashTable Symbol Nonnegative-Integer)(make-hash))
  (for ([x vars])(cond [(monomoid-has? b2 x) => (λ (i) (hash-set! k-map x i))]))
  (define (remap1 [k : Monomoid-Exponents])(list->monomoid (append (monomoid->list k) dif)))
  (define (remap2 [k : Monomoid-Exponents]) : Monomoid-Exponents
    (list->monomoid (for/list : (Listof Nonnegative-Integer)
               ([x vars])
               (cond [(hash-ref k-map x #f) => (λ (i) (monomoid-ref k i))]
                     [else 0]))))
  (values vars remap1 remap2))

(define (monomoid-substitute [b1 : Monomoid-Base][var : Symbol][b2 : Monomoid-Base])
  : (Values Monomoid-Base
            Nonnegative-Integer
            (-> Monomoid-Exponents Monomoid-Exponents)
            (-> Monomoid-Exponents Monomoid-Exponents))
  (define nr (monomoid-has? b1 var))
  (cond
    [nr
     (define-values (a b)(split-at (monomoid->list b1) nr))
     (define b1* (list->monomoid (append a (cdr b))))
     (define (remove [e1 : Monomoid-Exponents]) : Monomoid-Exponents
       (define-values (a b)(split-at (monomoid->list e1) nr))
       (list->monomoid (append a (cdr b))))
     (define-values (vars rebase1 rebase2)(monomoid-combine b1* b2))
     (values vars
             nr
             (λ ([b1 : Monomoid-Exponents]) : Monomoid-Exponents
               (rebase1 (remove b1)))
             rebase2)]
    [else
     (raise-argument-error 'monomoid-substitute (format "Var of first base ~a" b1) var)]))

(define (monomoid-exponents* [e0 : Monomoid-Exponents][e1 : Monomoid-Exponents]) : Monomoid-Exponents
  (unless (= (monomoid-length e0)(monomoid-length e1)) (raise-argument-error 'e+ "monomoid-exponent-sets should have equal length" (list '≠ e0 e1)))
  (for/vector : Monomoid-Exponents
    ([e0i (in-vector e0)]
     [e1i (in-vector e1)])
    (+ e0i e1i)))