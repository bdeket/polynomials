#lang typed/racket/base

(require typed/rackunit)
(require "poly-struct.rkt")

;make-poly: no explicit tests

;poly-degree
(check-equal? (poly-degree (make-poly C-algebra '(((1) 1)))) 1)
(check-equal? (poly-degree (make-poly C-algebra '(((1) 0)))) 0)
(check-equal? (poly-degree (make-poly C-algebra '(((2) 1)))) 2)
(check-equal? (poly-degree (make-poly C-algebra '(((2 3) 1)((1 2) 1)))) 3)
(check-equal? (poly-degree (make-poly C-algebra '(((2 3) 0)((1 2) 1)))) 2)

(check-exn exn:fail? (λ ()(poly-degree (make-poly C-algebra '(((2) 1)) (monomoid 'x 'y 'z)))))

;poly-coefficient
(check-equal? (poly-coefficient (make-poly C-algebra '(((2 3) 1)((1 2) 1))) (monomoid 2 3)) 1)
(check-equal? (poly-coefficient (make-poly C-algebra '(((2 3) 1)((1 2) 1))) (monomoid 1 2)) 1)

(check-exn exn:fail? (λ ()(poly-coefficient (make-poly C-algebra '(((2 3) 1)((1 2) 1))) (monomoid 1))))
(check-exn exn:fail? (λ ()(poly-coefficient (make-poly C-algebra '(((0) 1)((1) 1)((2) 1))) (monomoid 2 3))))
(check-exn exn:fail? (λ ()(poly-coefficient (make-poly C-algebra '(((0 0) 1)((1 0) 1)((2 0) 1))) (monomoid 2 3 0))))
(check-exn exn:fail? (λ ()(poly-coefficient (make-poly C-algebra '(((0 0) 1)((1 0) 1)((2 0) 1))) (monomoid 2))))

;poly-vars && poly-vars-len
(check-equal? (poly-vars (make-poly C-algebra '(((1) 1)))) (monomoid 'x))
(check-equal? (poly-vars-len (make-poly C-algebra '(((1) 1)))) 1)
(check-equal? (poly-vars (make-poly C-algebra '(((1 2 3) 1)))) (monomoid 'x_0 'x_1 'x_2))
(check-equal? (poly-vars-len (make-poly C-algebra '(((1 2 3) 1)))) 3)
(check-equal? (poly-vars (make-poly C-algebra '(((1 2 3) 1)) (monomoid 'x 'y 'z))) (monomoid 'x 'y 'z))
(check-equal? (poly-vars-len (make-poly C-algebra '(((1 2 3) 1)))) 3)

;poly-=
(check-true (poly-= C-algebra (make-poly C-algebra '(((1) 1))) (make-poly C-algebra '(((1) 1)))))
(check-true (poly-= C-algebra (make-poly C-algebra '(((1) 1)((2)0))) (make-poly C-algebra '(((1) 1)))))
(check-false (poly-= C-algebra (make-poly C-algebra '(((1) 1)) (monomoid 'y)) (make-poly C-algebra '(((1) 1)))))
(check-false (poly-= C-algebra (make-poly C-algebra '(((1) 2)) (monomoid 'y)) (make-poly C-algebra '(((1) 1)))))
(check-false (poly-= C-algebra (make-poly C-algebra '(((2) 1)) (monomoid 'y)) (make-poly C-algebra '(((1) 1)))))

;poly-copy
(check-true (let* ([P1 (make-poly C-algebra '(((1) 1)))]
                   [P2 (poly-copy P1)])
              (and (not (eq? P1 P2)) (poly-= C-algebra P1 P2))))

;poly-set
(check-true (let ([P1 (make-poly C-algebra '(((1) 1)))]
                  [P2 (make-poly C-algebra '(((1) 1)((0) 2)))]
                  [k (monomoid 0)])
              (poly-= C-algebra (poly-set P1 k 2) P2)))
(check-exn exn:fail? (let ([P1 (make-poly C-algebra '(((1) 1)))]
                           [k (monomoid 2)])
                       (λ()(poly-set P1 k 1))))

;in-coefficients
;poly-coefficient
;poly->string
;poly-1-map
;poly-2-map
;poly-n-map
;poly-remap
;poly-realg
;poly-remove-unused-base-vars
;poly+
;poly-scale
;poly*
;poly-
;poly-quotient/remainder
;poly-expt
;poly-substitute
;poly-diff poly-int
;poly-evaluate
;poly-from-roots
;with-algebra
;(all-from-out "algebra.rkt")
;monomoid