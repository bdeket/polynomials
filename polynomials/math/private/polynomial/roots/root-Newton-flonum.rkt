#lang typed/racket/base

(require math/flonum)
(require "../poly-flonum.rkt"
         "root-helpers.rkt")

(provide (all-defined-out))

(define (Newton-flroot [P : flpoly]
                       [x_0 : (U Flonum (List Flonum Flonum)) 0.0]
                       #:checkΔ [Δfct : flEndFct flendfct]
                       #:iterations [iterations : Positive-Integer 100]
                       #:poly-eval [Peval : (-> flpoly Flonum Flonum) flHorner]) : (flresult Flonum)
  (define dP (flpoly-diff P))
  (let loop : (flresult Flonum)
    ([i   : Integer 0]
     [x_k : Flonum (if (list? x_0) (fl/ (fl+ (car x_0)(cadr x_0))2.0) x_0)]
     [Δx_k-1 : Flonum +inf.0]
     [lst : (Listof (List Flonum Flonum)) '()])
    (define y_k (Peval P x_k))
    (define lst+ (cons (list x_k y_k) lst))
    (cond
      [(Δfct lst+) (flresult x_k 'done i lst+)]
      [(< iterations i) (flresult x_k 'max-iterations i lst+)]
      [else
       (define z_k (Peval dP x_k))
       (cond
         [(= z_k 0)
          (flresult x_k 'local-extremum i lst+)]
         [else
          (define δ (/ y_k z_k))
          (loop (+ i 1) (- x_k δ) δ lst+)])])))
(module+ test
  (require typed/rackunit)
  (define flpoly> flpoly/descending)
  (check-= (flresult-root (Newton-flroot (flpoly> 1.0 -1.0))) 1.0 1e-16)
  (check-= (flresult-root (Newton-flroot (flpoly-from-roots 3.0 -2.0) 2.0)) 3.0 1e-16)
  (check-= (flresult-root (Newton-flroot (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397) -2.0))
           -2.632993161855452   1e-16)
  (check-= (flresult-root (Newton-flroot (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397) -1.5))
           -0.18350341907227397 1e-8))
