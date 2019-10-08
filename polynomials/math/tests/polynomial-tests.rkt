#lang typed/racket/base

(require typed/rackunit)

;------------------------------------------------------------------------------------
;-  tests for flpoly
;------------------------------------------------------------------------------------
(require math/private/polynomial/poly-flonum
         math/flonum)

;  Constructors/accessors
(check-equal? (flpoly> 0.0 1.1 2.2 3.3) (flpoly< 3.3 2.2 1.1 0.0))
(check-equal? (flpoly-degree (flpoly> 0.0 1.1 2.2 3.3)) 2)
(check-equal? (flpoly-coefficient (flpoly> 3.3 2.2 1.1 0.0) 2) 2.2)
(check-equal? (flpoly-coefficient (flpoly< 0.0 1.1 2.2 3.3) 2) 2.2)
(check-equal? (flpoly-coefficient (flpoly< 0.0 1.1 2.2 3.3) 8) 0.0)
(check-equal? (flpoly-reverse-coefficient (flpoly> 3.3 2.2 1.1 0.0) 2) 1.1)
(check-equal? (flpoly-reverse-coefficient (flpoly< 0.0 1.1 2.2 3.3) 2) 1.1)
(check-equal? (flpoly-reverse-coefficient (flpoly< 0.0 1.1 2.2 3.3) 8) 0.0)
(check-equal? (flpoly> 0.0 0.0 0.0 1.1 0.1) (flpoly< 0.1 1.1))
(check-equal? (flpoly-from-roots 1.0 1.0 1.0 1.0) (flpoly> 1.0 -4.0 6.0 -4.0 1.0))

;  Evaluator
(check-equal? (compensatedHorner (flpoly> 1.0 2.0 1.0) 0.0) 1.0)
(check-equal? (compensatedHorner (flpoly> 1.0 2.0 1.0) 1.0) 4.0)
(check-equal? (Horner+ (flpoly> 1.0 2.0 1.0) 1.0) 4.0)
(check-equal? (Horner (flpoly> 1.0 2.0 1.0) 1.0) 4.0)
(let ([P (flpoly> 1.0 1.0 0.0 0.0 3.0 1.0)])
  (check-equal? (compensatedHorner P 0.0) (Horner P 0.0))
  (check-equal? (compensatedHorner P 1.0) (Horner P 1.0)))
;(check-equal? (complexHorner (flpoly> 1.0 2.0 1.0) +i) 0.0+2.0i)

;  Sum
(check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> 2.0 8.0)) (flpoly> 4.0 5.0 10.0))
(check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> -4.0 2.0 8.0)) (flpoly> 5.0 10.0))
(check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> -4.0 -3.0 -2.0)) flpoly-zero)
(check-equal? (flpoly+ (flpoly< 1.0 0.0) (flpoly< 1e-16 0.0)(flpoly< 1e-16 0.0)) (flpoly< 1.0000000000000002 0.0))

;  Difference
(check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 2.0 8.0)) (flpoly> 4.0 1.0 -6.0))
(check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 4.0 2.0 8.0)) (flpoly> 1.0 -6.0))
(check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 4.0 3.0 2.0)) flpoly-zero)
(check-equal? (flpoly- (flpoly< 1e-16)(flpoly< -1.0)(flpoly< -1e-16)) (flpoly> 1.0000000000000002))

;  Product
(check-equal? (flpoly*s (flpoly> 4.0 3.0 2.0) 2.0) (flpoly> 8.0 6.0 4.0))
(check-equal? (flpoly*p (flpoly> 4.0 1.0)(flpoly> 2.0 2.0)) (flpoly> 8.0 10.0 2.0))
(check-equal? (flpoly*-accurate  (flpoly> 4.0 1.0)(flpoly> 2.0 2.0)) (flpoly> 8.0 10.0 2.0))
(check-equal? (flpoly*p (flpoly> 1.0 1.0)(flpoly*p (flpoly> 1.0 1.0)(flpoly> 1.0 1.0))) (flpoly> 1.0 3.0 3.0 1.0))
(check-equal? (flpoly*-accurate  (flpoly> 1.0 1.0)(flpoly> 1.0 1.0)(flpoly> 1.0 1.0)) (flpoly> 1.0 3.0 3.0 1.0))
(check-equal? (flpoly*-accurate  (flpoly> 4.0 8.0 1.0)(flpoly> 2.0 2.0 .5 .4))
              (flpoly*p (flpoly> 4.0 8.0 1.0)(flpoly> 2.0 2.0 .5 .4)))

;  Exponent
(check-equal? (flpoly-expt (flpoly> 1.0 2.0) 0) flpoly-one)
(check-equal? (flpoly-expt (flpoly> 1.0 2.0) 1) (flpoly> 1.0 2.0))
(check-equal? (flpoly-expt (flpoly> 1.0 2.0) 2) (flpoly> 1.0 4.0 4.0))
(check-equal? (flpoly-expt (flpoly> 1.0 1.0) 5) (flpoly> 1.0 5.0 10.0 10.0 5.0 1.0))

;  Substitute
(check-equal? (flpoly-subst (flpoly> 1.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 2.0 1.0))
(check-equal? (flpoly-subst (flpoly> 1.0 0.0 0.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 4.0 6.0 4.0 1.0))
(check-equal? (flpoly-subst (flpoly> 1.0 0.0 2.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 4.0 8.0 8.0 3.0))

;  Shift
(check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) 0) (flpoly> 4.0 3.0 2.0))
(check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) 2) (flpoly> 4.0 3.0 2.0 0.0 0.0))
(check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) -2) (flpoly> 4.0))
(check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) -3) (flpoly> 0.0))

;  Diff
(check-equal? (flpoly-diff (flpoly> 1.0 1.0 1.0 1.0) 1) (flpoly> 3.0 2.0 1.0))
(check-equal? (flpoly-diff (flpoly> 1.0 1.0 1.0 1.0) 2) (flpoly> 6.0 2.0))
(check-equal? (flpoly-diff (flpoly> 1.0 1.0) 3) flpoly-zero)

;  Int
(check-equal? (flpoly-int (flpoly> 1.0 1.0 1.0 1.0) 1) (flpoly> (fl 1/4) (fl 1/3) (fl 1/2) 1.0 0.0))
(check-equal? (flpoly-int (flpoly> 1.0 1.0 1.0) 2) (flpoly> (fl 1/12) (fl 1/6) (fl 1/2) 0.0 0.0))

;  Division
(let ([P (flpoly> 1.0 2.0 1.0)]
      [/p (flpoly> 1.0 1.0)])
  (define-values (Q R) (flpoly/p-QR P /p))
  (check-equal? Q (flpoly> 1.0 1.0))
  (check-equal? (flpoly-degree R) 0)
  (check-= (flpoly-coefficient R 0) 0 1e-16))
(let ([P (flpoly> 1.0 3.0 3.0 1.0)]
      [/p (flpoly> 1.0 1.0)])
  (define-values (Q R) (flpoly/p-QR P /p))
  (check-equal? Q (flpoly> 1.0 2.0 1.0))
  (check-equal? (flpoly-degree R) 0)
  (check-= (flpoly-coefficient R 0) 0 1e-16))
(let ([P (flpoly> 1.0 3.0 4.0 2.0)]
      [/p (flpoly> 1.0 2.0 1.0)])
  (define-values (Q R) (flpoly/p-QR P /p))
  (check-equal? Q (flpoly> 1.0 1.0))
  (check-equal? R (flpoly> 1.0 1.0)))
(let ([P (flpoly> 1.0 2.0 1.0)]
      [r -1.0])
  (define-values (Q R) (flpoly-reduce-root-QR P r))
  (check-equal? Q (flpoly> 1.0 1.0))
  (check-= R 0 1e-16))
(let ([P (flpoly> 1.0)]
      [r -1.0])
  (define-values (Q R) (flpoly-reduce-root-QR P r))
  (check-equal? Q flpoly-zero)
  (check-= R 0 1.0))
(let ([P (flpoly> 1.0 3.0 3.0 1.0)]
      [r -1.0])
  (define-values (Q R) (flpoly-reduce-root-QR P r))
  (check-equal? Q (flpoly> 1.0 2.0 1.0))
  (check-= R 0 1e-16))
(let ([P (flpoly> 5.0 2.0 -3.0)]
      [r 3.0])
  (define-values (Q R) (flpoly-reduce-root-QR P r))
  (check-equal? Q (flpoly> 5.0 17.0))
  (check-= R 48 1e-16))

;  Absolute coefficients
(check-equal? (flpoly->absolute-coefficients (flpoly> -1.0 2.0 -1.0)) (flpoly> 1.0 2.0 1.0))
