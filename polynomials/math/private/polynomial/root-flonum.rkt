#lang typed/racket/base

(require math/flonum
         (only-in racket/math conjugate))
(require "poly-flonum.rkt"
         "roots/root-helpers.rkt"
         "roots/root-bounds.rkt"
         "roots/root-closedform.rkt"
         "roots/root-Newton-flonum.rkt"
         "roots/root-JT-flonum.rkt")
(provide (all-from-out
          "poly-flonum.rkt"
          "roots/root-helpers.rkt"
          "roots/root-bounds.rkt"
          "roots/root-closedform.rkt"
          "roots/root-Newton-flonum.rkt"
          "roots/root-JT-flonum.rkt"))

;------------------------------------
;iterative 1-root finders
;------------------------------------
(define (bisect-flroot [P : flpoly]
                       [x_0 : (U Flonum (List Flonum Flonum)) (roots-interval P)]
                       #:checkΔ [Δfct : flEndFct flendfct]
                       #:iterations [iterations : Positive-Integer 100]
                       #:poly-eval [Peval : (-> flpoly Flonum Flonum) Horner]) : (flresult Flonum)
  (define (Pfct [x : Flonum])(Peval P x))
  (define (inner [i : Integer][x- : Flonum][y- : Flonum][x+ : Flonum][y+ : Flonum][lst : (Listof (List Flonum Flonum))]) : (flresult Flonum)
    (define xm (fl/ (fl+ x- x+) 2.0))
    (define ym (Pfct xm))
    (define lst+ (cons (list xm ym) lst))
    (cond
      [(Δfct lst+) (flresult xm 'done i lst+)]
      [(< iterations i) (flresult xm 'max-iterations i lst+)]
      [(<= (fl* y- ym) 0)
       (inner (+ i 1) x- y- xm ym lst+)]
      [else
       (inner (+ i 1) xm ym x+ y+ lst+)]))

  (make-and-start-bracket P Pfct x_0 (λ ([x- : Flonum][y- : Flonum][x+ : Flonum][y+ : Flonum])(fl/ (fl+ x- x+) 2.0)) inner))

(define (secant-flroot [P : flpoly]
                       [x_0 : (U Flonum (List Flonum Flonum)) (roots-interval P)]
                       #:checkΔ [Δfct : flEndFct flendfct]
                       #:iterations [iterations : Positive-Integer 100]
                       #:poly-eval [Peval : (-> flpoly Flonum Flonum) Horner]) : (flresult Flonum)
  (define (Pfct [x : Flonum])(Peval P x))
  (define (f [x- : Flonum][y- : Flonum][x+ : Flonum][y+ : Flonum]) (fl- x+ (fl* y+ (fl/ (fl- x+ x-)(fl- y+ y-)))))
  (define (inner [i : Integer][x- : Flonum][y- : Flonum][x+ : Flonum][y+ : Flonum][lst : (Listof (List Flonum Flonum))]) : (flresult Flonum)
    (define xm (f x- y- x+ y+))
    (define ym (Peval P xm))
    (define lst+ (cons (list xm ym) lst))
;(println (list i x- y- x+ y+ xm ym (fl- xm (if (fl< (fl* y- ym) 0.0) x+ x-))))
    (cond
      [(Δfct lst+) (flresult xm 'done i lst+)]
      [(< iterations i) (flresult xm 'max-iterations i lst+)]
      [(<= (fl* y- ym) 0)
       (inner (+ i 1) x- y- xm ym lst+)]
      [else
       (inner (+ i 1) xm ym x+ y+ lst+)]))

  (make-and-start-bracket P Pfct x_0 f inner))

(define (Müller-flroot [P : flpoly]
                       [x_0 : (U Flonum (List Flonum Flonum)) 0.0]
                       #:checkΔ [Δfct : EndFct endfct]
                       #:iterations [iterations : Positive-Integer 100]
                       #:poly-eval [Peval : (case-> (-> flpoly Flonum Flonum)(-> flpoly Number Number)) complexHorner]) : (flresult Number)
  (define (Pfct [x : Number])(Peval P x))
  (define (inner [i : Integer]
                 [x0 : Number][y0 : Number ]
                 [x1 : Number][y1 : Number ]
                 [x2 : Number][y2 : Number ]
                 [lst : (Listof (List Number Number))]) : (flresult Number)
    (define q (/ (- x2 x1)(- x1 x0)))
    (define A (+ (* q y2) (* -1 q (+ 1 q) y1) (* q q y0)))
    (define B (+ (* (+ (* 2 q) 1) y2) (* -1 (expt (+ 1 q) 2) y1) (* q q y0)))
    (define C (* (+ 1 q) y2))
    (define D (sqrt (- (* B B) (* 4 A C))))
    (define Q1 (- B D))
    (define Q2 (+ B D))
    (define Q (if (< (magnitude Q1)(magnitude Q2))Q2 Q1))
    (define δ (* (- x2 x1)(/ (* 2 C) Q)))
    (define x3 (- x2 δ))
    (define y3 (Pfct x3))
    (define lst+ (cons (list x3 y3) lst))
    (cond
      [(<= iterations i) (flresult x3 'max-iterations i lst+)]
      [(Δfct lst+) (flresult x3 'done i lst+)]
      [else (inner (+ i 1) x1 y1 x2 y2 x3 y3 lst+)]))
  (define-values (x0 y0 x1 y1 x2 y2)
    (make-bracket P (λ ([x : Flonum]) (Peval P x)) x_0
                  (λ ([x- : Flonum][y- : Flonum][x+ : Flonum][y+ : Flonum])(fl/ (fl+ x- x+) 2.0))))
  (inner 0 x0 y0 x1 y1 x2 y2 (list (list x2 y2)(list x1 y1)(list x0 y0))))

(define (Laguerre-flroot [P : flpoly]
                         [x_0 : (U Number (List Number Number)) 0.0]
                         #:checkΔ [Δfct : EndFct endfct]
                         #:iterations [iterations : Positive-Integer 100]
                         #:poly-eval [Peval : (-> flpoly Number Number) complexHorner]) : (flresult Number)
  (define dP (flpoly-diff P))
  (define d²P (flpoly-diff dP))
  (define n (flpoly-degree P))
  (let loop : (flresult Number)
    ([i   : Integer 0]
     [x_k : Number (if (list? x_0) (/ (+ (car x_0)(cadr x_0)) 2.0) x_0)]
     [lst : (Listof (List Number Number)) '()])
    (define y_k (Peval P x_k))
    (define lst+ (cons (list x_k y_k) lst))
    (cond
      [(Δfct lst+) (flresult x_k 'done i lst+)]
      [(< iterations i) (flresult x_k 'max-iterations i lst+)]
      [else
       (define G (/ (Peval dP x_k) y_k))
       (define G² (* G G))
       (define H (- G² (/ (Peval d²P x_k) y_k)))
       (define D (sqrt (* (- n 1)(- (* n H) G²))))
       (define N+ (+ G D))
       (define N- (- G D))
       (define N (if (< (magnitude N+) (magnitude N-)) N- N+))
       (cond
         [(= N 0) (flresult x_k 'local-extremum i lst+)]
         [else
          (loop (+ i 1) (- x_k (/ n N)) lst+)])])))



;via eigenvalues

;------------------------------------
;allrootfinder
;------------------------------------
(define (flpoly-roots [P : flpoly]) : (U 'All (Listof Number))
(println (list 'flpoly-roots P))
  (define solvers (list bisect-flroot secant-flroot Newton-flroot Müller-flroot Laguerre-flroot JenkinsTraub-flroot))
  (define ans
    (let ans-loop : (U 'All (Listof Number))
      ([P* : flpoly (flpoly*s P (flpoly-bestscale P))]
       [intervals : (Listof (List Flonum Flonum)) '()]
       [ans : (Listof Number) '()])
(println (list '-> P* intervals ans))
      (cond
        [(= (flpoly-degree P*) 0) (flpoly-0°root P*)]
        [(= (flpoly-degree P*) 1) (append ans (flpoly-1°root P*))]
        [(= (flpoly-degree P*) 2) (append ans (flpoly-2°root P*))]
        [(= (flpoly-degree P*) 3) (append ans (flpoly-3°root P*))]
        [else
         (let root-loop ([rslt : (flresult Number) (Laguerre-flroot P*)])
(println (list '--> (flresult-root rslt)(flresult-endmsg rslt)))
           (define bounds (inspect-iterations rslt))
           (case (flresult-endmsg rslt)
             [(done algorithm-stopped)
              (define ri (flresult-root rslt))
              (cond
                [(flonum? (flresult-root rslt))
                 (define-values (Q R) (flpoly-reduce-root-QR P* ri))
                 (ans-loop Q bounds (cons ri ans))]
                [else
                 (define-values (Q R) (flpoly/p-QR P* (flpoly-from-complex-root ri)))
                 (ans-loop Q bounds (cons ri (cons (conjugate ri) ans)))])]
             [else
              (cond
                [(null? bounds)
                 (root-loop (Müller-flroot P*))]
                [(root-loop (Newton-flroot P* (car bounds)))])]))])))
(println (list '---> ans))
  (if (list? ans)
      (sort (map (λ ([x : Number]) (flresult-root (Laguerre-flroot P x))) ans) <)
      ans))

(module+ test
  (require racket/list)
  (define-syntax-rule (show r)
    (let ([R r])
      (printf "--------------------\n~a ~a in ~a\n~a\n~a\n"
              'r (flresult-endmsg R) (flresult-iterations R)
              (flresult-root R)
              (for/list : (Listof Any) ([l (in-list (flresult-iteration-values R))][i (in-range 5)]) l))))
  (define P (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))
  (define xp_0 -2.0)
  (show (bisect-flroot P xp_0))
  (show (secant-flroot P xp_0))
  (show (Newton-flroot P xp_0))
  (show (Müller-flroot P xp_0))
  (show (Laguerre-flroot P xp_0))
  (show (JenkinsTraub-flroot P xp_0))
  (displayln "--------------------")
  (define Q1 (flpoly-from-roots .9998 .9999 1.0 1.003 1.003))Q1
  (define Q2 (flpoly< -1.00570721742018 5.02282165484018 -10.03422165742 10.02280722 -5.0057 1.0))Q2
  (define Q Q2)
  (define xq_0 0.9)
  (show (bisect-flroot Q xq_0))
  (show (secant-flroot Q xq_0))
  (show (Newton-flroot Q xq_0))
  (show (Müller-flroot Q xq_0))
  (show (Laguerre-flroot Q xq_0))
  (show (JenkinsTraub-flroot Q))
  #|
  (displayln "--------------------")
  (require plot)
  (define x0 .999)(define x1 1.0035)
  (plot (list (function (λ ([x : Real]) (Horner Q (fl x))) x0 x1 #:color 1 #:label "H")
              (function (λ ([x : Real]) (compensatedHorner Q (fl x))) x0 x1 #:color 2 #:label "FL+")
              (function (λ ([x : Real]) (complexHorner Q (fl x))) x0 x1 #:color 3 #:label "0+i")
              (hrule 0 #:color 'black)))
  |#
  )
