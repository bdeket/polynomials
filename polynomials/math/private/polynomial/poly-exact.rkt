#lang typed/racket/base

(require "poly-mbase.rkt")

(provide (all-defined-out))

(make-poly-base e Exact-Rational
                inexact->exact = + - * /
                (λ ([L : (Listof Exact-Rational)])(apply + L)))
(make-poly-realfct e Exact-Rational
                   epoly epoly-v epoly-degree epoly*
                   Exact-Number real-part imag-part make-rectangular
                   inexact->exact = + - * /
                   (λ ([L : (Listof Exact-Rational)])(apply + L))
                   abs)

(module+ test
  (epoly-const 3/8)
  epoly-zero
  epoly-one
  (epoly-copy epoly-zero)
  (epolyV< #[0 1 2 3/4 0])
  (epoly> 5 4 3 2 1 0)

  (epoly+ (epoly> 5 4 3 2 1 0)
          (epoly> 0 1 2 3 4 5)
          (epoly> 1 3 5 5 3 1))

  (epoly* (epoly> 5 4 3 2 1 0)
          (epoly> 0 1 2 3 4 5)
          (epoly> 1 3 5 5 3 1))

  (epoly-from-roots  9998/1000
                     9999/1000
                     1
                     10003/1000
                     10003/1000)

  (epoly-reduce-root-QR (epoly-from-roots  9998/1000
                                           9999/1000
                                           1
                                           10003/1000
                                           10003/1000)
                        1)

  (epoly-reduce-root-QR (epoly-from-roots  9998/1000
                                           9999/1000
                                           1
                                           10003/1000
                                           10003/1000)
                        9998/1000)

  (epoly-from-roots 1/2
                    (make-rectangular 1/3 1/4)
                    (make-rectangular 1/3 -1/4)))