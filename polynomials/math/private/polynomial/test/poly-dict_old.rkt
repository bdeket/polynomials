#lang typed/racket/base

(require racket/sequence
         racket/vector)
(require "monomoid.rkt")

(provide (all-defined-out))
;***********************************************************************************************************************
;* Poly-dict: mapping monomoid to coefficients                                                                         *
;***********************************************************************************************************************
(define-type p-dict (All (TheType) (case-> (Monomoid-Exponents -> TheType)
                                           (      -> (Sequenceof Monomoid-Exponents TheType))
                                           
                                           ('get 'size -> Nonnegative-Integer)
                                           ('get 'copy -> (p-dict TheType))
                                           ('get 'list -> (Listof (List Monomoid-Exponents TheType)))
                                           ('get Symbol -> Any)
                                           ('set Monomoid-Exponents TheType -> (p-dict TheType)))))

(: make-dense-dict (All (TheType) ((Vectorof TheType) TheType -> (p-dict TheType))))
(define (make-dense-dict V* zero)
  (define V (vector->immutable-vector V*))
  (case-lambda
      [(x) (define i (monomoid-first x))
           (if (< -1 i (vector-length V)) (vector-ref V (monomoid-first x)) zero)]
      [() (in-parallel ((inst sequence-map Monomoid-Exponents Nonnegative-Integer)
                        (λ ([x : Nonnegative-Integer]) : Monomoid-Exponents (monomoid x))
                        (in-naturals))
                       (in-vector V))]
      [(get x)
       (case x
         [(size)(vector-length V)]
         [(copy)(make-dense-dict V zero)]
         [(list)(for/list : (Listof (List Monomoid-Exponents TheType))
                  ([i : Nonnegative-Integer (in-naturals)]
                   [v (in-vector V)])
                  (list (monomoid i) v))])]
      [(set i v)
       (define V+ (vector-copy V))
       (vector-set! V+ (monomoid-first i) v)
       (make-dense-dict V+ zero)]))

(: make-dense-dict2 (All (TheType) ((Vectorof TheType) TheType -> (p-dict TheType))))
(define (make-dense-dict2 V zero)
  (case-lambda
    [(x) (define i (monomoid-first x))
         (if (< -1 i (vector-length V)) (vector-ref V (monomoid-first x)) zero)]
    [() (in-parallel ((inst sequence-map Monomoid-Exponents Nonnegative-Integer)
                      (λ ([x : Nonnegative-Integer]) : Monomoid-Exponents (monomoid x))
                      (in-naturals))
                     (in-vector V))]
    [(get x)
     (case x
       [(size)(vector-length V)]
       [(copy)(make-dense-dict2 (vector-copy V) zero)]
       [(list)(for/list : (Listof (List Monomoid-Exponents TheType))
                ([i : Nonnegative-Integer (in-naturals)]
                 [v (in-vector V)])
                (list (monomoid i) v))])]
    [(set i v)
     (define V+ (vector-copy V))
     (vector-set! V+ (monomoid-first i) v)
     (make-dense-dict2 V+ zero)]))

(: make-sparse-dict (All (TheType) ((HashTable Monomoid-Exponents TheType) TheType -> (p-dict TheType))))
(define (make-sparse-dict H zero)
  (case-lambda
    [(x) (hash-ref H x (λ () zero))]
    [() ((inst in-hash Monomoid-Exponents TheType) H)]
    [(get x)
     (case x
       [(size)(hash-count H)]
       [(copy)(make-sparse-dict (hash-copy H) zero)]
       [(list)(for/list : (Listof (List Monomoid-Exponents TheType))
                ([(k v)(in-hash H)])
                (list k v))])]
    [(set i v)
     (define H+ (hash-copy H))
     (hash-set! H+ i v)
     (make-sparse-dict H+ zero)]))
