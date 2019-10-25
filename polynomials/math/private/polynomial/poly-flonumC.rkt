#lang typed/racket/base

(require (only-in math/base float-complex?)
         math/flonum)
(require "poly-mbase.rkt")

(provide (all-defined-out))


(define (flc [a : Number]): Float-Complex (make-rectangular (fl (real-part a))(fl (imag-part a))))
(define (flcsum [L : (Listof Float-Complex)]) : Float-Complex (flc (apply + L)))
  
(make-poly-cplxfct [flc : Float-Complex]
                   flc + - * / #:= =)

(define (flcpoly->absolute-coefficients [P : flcPoly])
  (local-require "poly-flonum.rkt" math/flonum)
  (flpoly (for/vector : (Vectorof Flonum)
            ([v : Float-Complex (in-vector (flcpoly-v P))])(fl (magnitude v)))
          (flcpoly-degree P)))

(module+ test
  (define flcpoly> flcpoly/descending)
  (flcpoly-constant (flc 3/8))
  flcpoly-zero
  flcpoly-one
  (flcpoly-copy flcpoly-zero)
  (flcvector/ascending->poly (vector (flc 0) (flc 1) (flc 2) (flc 3/4) (flc 0)))
  (flcpoly> (flc 5) (flc 4) (flc 3) (flc 2) (flc 1) (flc 0))

  (flcpoly+ (flcpoly> (flc 5) (flc 4) (flc 3) (flc 2) (flc 1) (flc 0))
           (flcpoly> (flc 0) (flc 1) (flc 2+i) (flc 3) (flc 4) (flc 5))
           (flcpoly> (flc 1) (flc 3) (flc 5) (flc 5) (flc 3) (flc 1)))

  (flcpoly* (flcpoly> (flc 5) (flc 4) (flc 3) (flc 2) (flc 1) (flc 0))
           (flcpoly> (flc 0) (flc 1) (flc 2+i) (flc 3) (flc 4) (flc 5))
           (flcpoly> (flc 1) (flc 3) (flc 5) (flc 5) (flc 3) (flc 1)))

  (flcpoly-from-roots  (flc 9998/1000)
                      (flc 9999/1000)
                      (flc 1)
                      (flc 10003/1000)
                      (flc 10003/1000))

  (flcpoly-reduce-root-QR (flcpoly-from-roots (flc 9998/1000)
                                            (flc 9999/1000)
                                            (flc 1)
                                            (flc 10003/1000)
                                            (flc 10003/1000))
                         1.0+0.0i)

  (flcpoly-reduce-root-QR (flcpoly-from-roots (flc 9998/1000)
                                            (flc 9999/1000)
                                            (flc 1+i)
                                            (flc 10003/1000)
                                            (flc 10003/1000))
                         (flc 9998/1000))

  (flcpoly-from-roots (flc 1/2)
                     (make-rectangular (fl 1/3) (fl 1/4))
                     (make-rectangular (fl 1/3) (fl -1/3))))