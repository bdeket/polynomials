#lang typed/racket/base

(require racket/list)

(provide (except-out (all-defined-out) checked-list->monomoid))
;***********************************************************************************************************************
;* Monomoid                                                                                                            *
;***********************************************************************************************************************
(define-type Monomoid-Exponents (Vectorof Nonnegative-Integer))
(define-type Monomoid-Base (Vectorof Symbol))
(: monomoid (case-> (->* () #:rest Nonnegative-Integer Monomoid-Exponents)
                    (->* () #:rest Symbol Monomoid-Base)))
(define (monomoid . x)
  (cond
    [(empty? x)(raise-argument-error 'monomoid "At least one element" x)]
    [(and (symbol? (car x))(check-duplicates x))
     (raise-argument-error 'monomoid "Unique symbols for a base" x)]
    [else (list->vector x)]))
(define (monomoid-base->zero-exponent [b : Monomoid-Base]): Monomoid-Exponents (make-vector (monomoid-length b) 0))
(define monomoid-x (monomoid 'x))
(define monomoid-0 (monomoid 0))
(define (make-monomoid-base [i : Nonnegative-Integer]) : Monomoid-Base
  (for/vector : Monomoid-Base
    ([i (in-range i)])
    (string->symbol (format "x_~a" i))))


(: list->monomoid (case-> (-> (Listof Nonnegative-Integer) Monomoid-Exponents)(-> (Listof Symbol) Monomoid-Base)))
(define (list->monomoid l) (apply monomoid l))

(: checked-list->monomoid (case-> (-> (Listof Nonnegative-Integer) Monomoid-Exponents)(-> (Listof Symbol) Monomoid-Base)))
(define (checked-list->monomoid l) (list->vector l))

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

(define (monomoid-combine . [bs : Monomoid-Base *]) : (Values Monomoid-Base (Listof (-> Monomoid-Exponents Monomoid-Exponents)))
  (define vars (checked-list->monomoid (remove-duplicates (apply append (map monomoid->list bs)))))
  (define vars-len (monomoid-length vars))
  (values vars
          (for/list : (Listof (-> Monomoid-Exponents Monomoid-Exponents))
            ([b (in-list bs)])
            (define k-map : (HashTable Symbol Nonnegative-Integer)(make-hash))
            (for ([x vars])(cond [(monomoid-has? b x) => (λ (i) (hash-set! k-map x i))]))
            (define (remap [k : Monomoid-Exponents])
              (checked-list->monomoid
               (for/list : (Listof Nonnegative-Integer)
                 ([x vars])
                 (cond
                   [(hash-ref k-map x #f) => (λ (i) (monomoid-ref k i))]
                   [else 0]))))
            remap)))

(define (monomoid-substitute [b1 : Monomoid-Base][var : Symbol][b2 : Monomoid-Base])
  : (Values Monomoid-Base
            Nonnegative-Integer
            (-> Monomoid-Exponents Monomoid-Exponents)
            (-> Monomoid-Exponents Monomoid-Exponents))
  (define nr (monomoid-has? b1 var))
  (cond
    [nr
     (define-values (a b)(split-at (monomoid->list b1) nr))
     (define b1* (checked-list->monomoid (append a (cdr b))))
     (define (remove [e1 : Monomoid-Exponents]) : Monomoid-Exponents
       (define-values (a b)(split-at (monomoid->list e1) nr))
       (checked-list->monomoid (append a (cdr b))))
     (define-values (vars rs)(monomoid-combine b1* b2))
     (values vars
             nr
             (λ ([b1 : Monomoid-Exponents]) : Monomoid-Exponents
               ((list-ref rs 0) (remove b1)))
             (list-ref rs 1))]
    [else
     (raise-argument-error 'monomoid-substitute (format "Var of first base ~a" b1) var)]))

(define (monomoid-exponents* [e0 : Monomoid-Exponents][e1 : Monomoid-Exponents]) : Monomoid-Exponents
  (unless (= (monomoid-length e0)(monomoid-length e1)) (raise-argument-error 'e+ "monomoid-exponent-sets should have equal length" (list '≠ e0 e1)))
  (for/vector : Monomoid-Exponents
    ([e0i (in-vector e0)]
     [e1i (in-vector e1)])
    (+ e0i e1i)))