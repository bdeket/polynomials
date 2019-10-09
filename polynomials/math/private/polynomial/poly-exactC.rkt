#lang typed/racket/base

(require "poly-mbase.rkt")

(provide (except-out (all-defined-out) e* e/))

; Why is (* Exact-Number Exact-Number) not an Exact-Number?
(define (e* [e1 : Exact-Number][e2 : Exact-Number]) : Exact-Number 
  (make-rectangular
   (- (* (real-part e1)(real-part e2))
      (* (imag-part e1)(imag-part e2)))
   (+ (* (imag-part e1)(real-part e2))
      (* (real-part e1)(imag-part e2)))))
; Why is (/ Exact-Number Exact-Number) not an Exact-Number?
(define (e/ [e1 : Exact-Number][e2 : Exact-Number]) : Exact-Number
  (define d (- (* (real-part e2)(real-part e2))
               (* (imag-part e2)(imag-part e2))))
  (make-rectangular
   (/ (+ (* (real-part e1)(real-part e2))
         (* (imag-part e1)(imag-part e2)))
      d)
   (/ (- (* (imag-part e1)(real-part e2))
         (* (real-part e1)(imag-part e2)))
      d)))

(make-poly-base ec Exact-Number
                inexact->exact = + - e* e/
                (λ ([L : (Listof Exact-Number)])(apply + L)))
(make-poly-cplxfct ec Exact-Number
                   ecpoly ecpoly-v ecpoly-degree ecpoly*
                   inexact->exact = + - e* e/
                   (λ ([L : (Listof Exact-Number)])(apply + L)))

(define (ecpoly->absolute-coefficients [P : ecpoly])
  (local-require "poly-flonum.rkt" math/flonum)
  (flpoly (for/vector : (Vectorof Flonum)
            ([v : Exact-Number (in-vector (ecpoly-v P))])(fl (magnitude v)))
          (ecpoly-degree P)))

(module+ test
  (ecpoly-const 3/8+i)
  ecpoly-zero
  ecpoly-one
  (ecpoly-copy ecpoly-zero)
  (ecpolyV< #[0 1 2 3/4 0])
  (ecpoly> 5 4 3 2 1 0)

  (ecpoly+ (ecpoly> 5 4 3 2 1 0)
           (ecpoly> 0 1 +2i 3 4 5)
           (ecpoly> 1 3 5 5 3 1))

  (ecpoly* (ecpoly> 5 4 3 2 1 0)
           (ecpoly> 0 1 +2i 3 4 5)
           (ecpoly> 1 3 5 5 3 1))

  (ecpoly-from-roots  9998/1000
                      9999/1000
                      1
                      10003/1000
                      10003/1000)

  (ecpoly-reduce-root-QR (ecpoly-from-roots  9998/1000
                                             9999/1000
                                             1+i
                                             10003/1000
                                             10003/1000)
                         1)

  (ecpoly-reduce-root-QR (ecpoly-from-roots  9998/1000
                                             9999/1000
                                             1+1/5i
                                             10003/1000
                                             10003/1000)
                         9998/1000)

  (ecpoly-from-roots 1/2
                     (make-rectangular 1/3 1/4)
                     (make-rectangular 1/3 -1/3)))