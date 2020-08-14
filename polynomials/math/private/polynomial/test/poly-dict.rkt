#lang typed/racket/base

(require racket/sequence
         racket/vector)
(require "monomoid.rkt")

(provide (all-defined-out))
;***********************************************************************************************************************
;* Poly-dict: mapping monomoid to coefficients                                                                         *
;***********************************************************************************************************************
(struct (A) p-dict ([term : (Monomoid-Exponents -> A)]
                    [sequence : (-> (Sequenceof Monomoid-Exponents A))]
                    [size : (-> Nonnegative-Integer)]
                    [copy : (-> (p-dict A))]
                    [list : (-> (Listof (List Monomoid-Exponents A)))]
                    [set : (Monomoid-Exponents A -> (p-dict A))]
                    [set! : (Monomoid-Exponents A -> (p-dict A))]))

(: make-dense-dict-i (All (A) ((Immutable-Vectorof A) A -> (p-dict A))))
(define (make-dense-dict-i V zero)
  (define (term [e : Monomoid-Exponents]) : A
    (define i (monomoid-first e))
    (if (< -1 i (vector-length V)) (vector-ref V i) zero))
  (define (sequence)
    (in-parallel ((inst sequence-map Monomoid-Exponents Nonnegative-Integer)
                  (λ ([x : Nonnegative-Integer]) : Monomoid-Exponents (monomoid x))
                  (in-naturals))
                 (in-vector V)))
  (define (size)(vector-length V))
  (define (copy) : (p-dict A) this);everything immutable... no point in creating a real copy... right ???
  (define (aslist) : (Listof (List Monomoid-Exponents A))
    (for/list ([i : Nonnegative-Integer  (in-range (vector-length V))]
               [v (in-vector V)])
      (list (monomoid i) v)))
  (define (set [e : Monomoid-Exponents][x : A]);there MUST be a better way to do this :/
    (define V* (vector-copy V))
    (vector-set! V* (monomoid-first e) x)
    (make-dense-dict-m (vector->immutable-vector V*) zero))
  (define (set! [e : Monomoid-Exponents][x : A])(error "make-dense-dict-i: set! not implemented"))

  (define this : (p-dict A)
    (p-dict term
            sequence
            size
            copy
            aslist
            set
            set!))
  this)

(: make-dense-dict (All (A) ((Vectorof A) A -> (p-dict A))))
(define (make-dense-dict V zero) (make-dense-dict-i (vector->immutable-vector V) zero))


(: make-dense-dict-m (All (A) ((Vectorof A) A -> (p-dict A))))
(define (make-dense-dict-m V zero)
  (define (term [e : Monomoid-Exponents]) : A
    (define i (monomoid-first e))
    (if (< -1 i (vector-length V)) (vector-ref V i) zero))
  (define (sequence)
    (in-parallel ((inst sequence-map Monomoid-Exponents Nonnegative-Integer)
                  (λ ([x : Nonnegative-Integer]) : Monomoid-Exponents (monomoid x))
                  (in-naturals))
                 (in-vector V)))
  (define (size)(vector-length V))
  (define (copy)(make-dense-dict-m (vector-copy V) zero))
  (define (aslist) : (Listof (List Monomoid-Exponents A))
    (for/list ([i : Nonnegative-Integer (in-range (vector-length V))]
               [v (in-vector V)])
      (list (monomoid i) v)))
  (define (set [e : Monomoid-Exponents][x : A])
    (define V* (vector-copy V))
    (vector-set! V* (monomoid-first e) x)
    (make-dense-dict-m V* zero))
  (define (set! [e : Monomoid-Exponents][x : A]) : (p-dict A)
    (vector-set! V (monomoid-first e) x)
    this)

  (define this : (p-dict A)
    (p-dict term
            sequence
            size
            copy
            aslist
            set
            set!))
  this)

(: make-sparse-dict-i (All (A) ((Immutable-HashTable Monomoid-Exponents A) A -> (p-dict A))))
(define (make-sparse-dict-i H zero)
  (define (term [e : Monomoid-Exponents]) (hash-ref H e (λ () zero)))
  (define (sequence) ((inst in-hash Monomoid-Exponents A) H))
  (define (size)(hash-count H))
  (define (copy) : (p-dict A) this)
  (define (aslist) : (Listof (List Monomoid-Exponents A))
    (for/list : (Listof (List Monomoid-Exponents A))
                ([(k v)(in-hash H)])
                (list k v)))
  (define (set [e : Monomoid-Exponents][x : A])
    (make-sparse-dict-i (hash-set H e x) zero))
  (define (set! [e : Monomoid-Exponents][x : A])(error "make-dense-dict-i: set! not implemented"))

  (define this : (p-dict A)
    (p-dict term
            sequence
            size
            copy
            aslist
            set
            set!))
  this)
(: make-sparse-dict-m (All (A) ((HashTable Monomoid-Exponents A) A -> (p-dict A))))
(define (make-sparse-dict-m H zero)
  (define (term [e : Monomoid-Exponents]) (hash-ref H e (λ () zero)))
  (define (sequence) ((inst in-hash Monomoid-Exponents A) H))
  (define (size)(hash-count H))
  (define (copy)(make-sparse-dict (hash-copy H) zero))
  (define (aslist) : (Listof (List Monomoid-Exponents A))
    (for/list : (Listof (List Monomoid-Exponents A))
                ([(k v)(in-hash H)])
                (list k v)))
  (define (set [e : Monomoid-Exponents][x : A])
    (define H+ (hash-copy H))
     (hash-set! H+ e x)
     (make-sparse-dict H+ zero))
  (define (set! [e : Monomoid-Exponents][x : A]) : (p-dict A)
    (hash-set! H e x)
    this)

  (define this : (p-dict A)
    (p-dict term
            sequence
            size
            copy
            aslist
            set
            set!))
  this)

(: make-sparse-dict (All (A) ((HashTable Monomoid-Exponents A) A -> (p-dict A))))
(define (make-sparse-dict H zero) (make-sparse-dict-i (make-immutable-hash (hash->list H)) zero))


