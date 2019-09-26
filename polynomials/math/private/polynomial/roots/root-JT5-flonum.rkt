#lang typed/racket/base

(require math/flonum
         racket/math
         racket/match)
(require "../poly-flonum.rkt")

(provide (all-defined-out))

(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))
(define +FLT_MIN (floating-point-bytes->real (bytes #b00000000 #b00000000 #b00000000 #b00000001)))
(define +FLT_MAX (floating-point-bytes->real (bytes #b11111111 #b11111111 #b11111111 #b01111110)))

(define-type TFlag (U 'calcSC:almost-factor 'calcSC:div-by-c 'calcSC:div-by-d))

(define RADFAC (/ pi.f 180));Degrees - to - radians conversion factor = pi/180

;P: degree N
;sP: degree N-1
;K: degree N-1
;sK: degree N-2


; CALCULATE THE ZEROS OF THE QUADRATIC A*Z**2+B1*Z+C.
; THE QUADRATIC FORMULA, MODIFIED TO AVOID
; OVERFLOW, IS USED TO FIND THE LARGER ZERO IF THE
; ZEROS ARE REAL AND BOTH ZEROS ARE COMPLEX.
; THE SMALLER REAL ZERO IS FOUND DIRECTLY FROM THE
; PRODUCT OF THE ZEROS C/A.
(define (Quad [P : flpoly]) :  (List (Pair Flonum Flonum) (Pair Flonum Flonum))
  (unless (= (flpoly-degree P) 2) (raise-argument-error 'Quad "not a quadratic" P))
  (define a0 (flpoly-coefficient P 0))
  (define a1 (flpoly-coefficient P 1))
  (define a2 (flpoly-coefficient P 2))
  (cond
    [(= a0 0) `((0.0 . 0.0) (,(fl* -1.0 (fl/ a1 a2)) . 0.0))]
    ;what if a2/a1/a0 ±inf.0
    [else
     (define a1/2 (fl/ a1 2.0))
     (define-values (D* E*)
       (cond
           [(fl< (flabs a1/2) (flabs a0))
            (define E0
              (cond
                [(fl< a0 0.0) (fl* -1.0 a2)]
                [else        a2]))
            (define E1 (fl- (fl* a1/2 (fl/ a1/2 (flabs a0))) E0))
            (values (fl* (flsqrt (flabs E1)) (flsqrt (flabs a0)))
                    E1)]
           [else
            (define E
              (let ([E (fl- 1.0 (fl* (fl/ a2 a1/2)(fl/ a0 a1/2)))])
                (cond
                  [(not (or (nan? E)(infinite? E))) E]
                  [else (fl- 1.0 (fl/ (fl/ (fl* a2 a0) a1/2) a1/2))])))
            (values (fl* (flsqrt (flabs E))(flabs a1/2))
                    E)]))
     ;compute Discriminant avoiding overflow
     (cond
       [(< E* 0)
        ;conjugate zeros
        (define R (- (/ a1/2 a2)))
        (define I (abs (/ D* a2)))
        (list (cons R I) (cons R (- I)))]
       [else
        ;real zeros
        (define D** (cond [(> a1/2 0) (- D*)][else D*]))
        (define Z1 (/ (- D** a1/2) a2))
        (cond
          [(= Z1 0) '((0.0 . 0.0) (0.0 . 0.0))]
          [else     `((,(/ (/ a0 Z1) a2) . 0.0) (,Z1 . 0.0))])])]))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision [P : flpoly][u : Flonum][v : Flonum])
  (define-values (qP rP)(flpoly/p-QR P (flpoly> 1.0 u v)))
  (list qP
        (flpoly-coefficient rP 0)
        (fl- (flpoly-coefficient rP 0)(fl* u (flpoly-coefficient rP 1)))
        (flpoly-coefficient rP 1)))

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
(define (calcSC [K : flpoly][a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (U (List 'calcSC:almost-factor flpoly Flonum Flonum Flonum)
       (List (U 'calcSC:div-by-c 'calcSC:div-by-d) flpoly Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum))
  ;Synthetic division of K by the quadratic 1, u, v
  (match-define (list qK c+ud c d)(QuadraticSyntheticDivision K u v))
  (cond
    [(and (fl<= (flabs c) (* epsilon100 (flabs (flpoly-coefficient K 0))))
          (fl<= (flabs d) (* epsilon100 (flabs (flpoly-coefficient K 1)))))
     ;type=3 indicates the quadratic is almost a factor of K
     (list 'calcSC:almost-factor qK c+ud c d)]
    [else
     (define h (* v b))
     (cond
       [(>= (abs d) (abs c))
        ;TYPE = 2 indicates that all formulas are divided by d
        (define e (/ a d))
        (define f (/ c d))
        (define g (* u b))
        (define a1 (- (* f b) a))
        (define a3 (+ (* e (+ g a)) (* h (/ b d))))
        (define a7 (+ h (* c+ud e)));(f+u)a=(c+ud)a/d=(c+ud)*e
        (list 'calcSC:div-by-d qK c+ud c d e f g h a1 a3 a7)]
       [else
        ;TYPE = 1 indicates that all formulas are divided by c
        (define e (/ a c))
        (define f (/ d c))
        (define g (* e u))
        (define a1 (- b (* a (/ d c))))
        (define a3 (+ (* e a) (* (+ g (/ h c)) b)))
        (define a7 (+ (* h f) (* c+ud e)));gd+a=eud+a=a(ud/c+1)=a/c(c+ud)=(c+ud)*e
        (list 'calcSC:div-by-c qK c+ud c d e f g h a1 a3 a7)])]))

;Computes the next K polynomials using the scalars computed in calcSC
(define (nextK [qP : flpoly][qK : flpoly]
               [tFlag : TFlag]
               [a : Flonum][b : Flonum][a1 : Flonum][a3 : Flonum][a7 : Flonum])
  : flpoly
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     ; use unscaled form of the recurrence
     (flpoly-shift qK -1)]
    [else
     (define temp (if (equal? tFlag 'calcSC:div-by-c) b a))
     (cond
       [(> (abs a1) (* epsilon10 (abs temp)))
        (define a7+ (/ a7 a1))
        (define a3+ (/ a3 a1))
        (flpoly+ qP
                 (flpoly*s (flpoly-shift qP -1) (- a7+))
                 (flpoly*s (flpoly-shift qK -1) a3+))]
       [else
        (flpoly+ (flpoly*s (flpoly-shift qP -1) (- a7))
                 (flpoly*s (flpoly-shift qK -1) a3))])]))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest [P : flpoly][K : flpoly]
                [tFlag : TFlag]
                [a : Flonum][b : Flonum][c : Flonum][d : Flonum][f : Flonum][g : Flonum][h : Flonum][u : Flonum][v : Flonum]
                [a1 : Flonum][a3 : Flonum][a7 : Flonum])
  : (List Flonum Flonum)
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     (list 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (cond
         [(not (equal? tFlag 'calcSC:div-by-d))
          (values (flsum (list a (fl* u b) (fl* h f)))
                  (fl+ c (fl* (fl+ u (fl* v f)) d)))]
         [else
          (values (fl+ (fl* (fl+ a g) f) h)
                  (fl+ (fl* (fl+ f u) c) (fl* v d)))]))

     (define b1 (fl* -1.0 (fl/ (flpoly-coefficient K 0)(flpoly-coefficient P 0))))
     (define b2 (fl* -1.0 (fl/ (fl+ (flpoly-coefficient K 1) (fl* b1 (flpoly-coefficient P 1))) (flpoly-coefficient P 0))))
     (define c1 (fl* (fl* v b2) a1))
     (define c2 (fl* b1 a7))
     (define c3 (fl* (fl* b1 b1) a3))
     (define c4 (fl+ (fl* -1.0 (fl+ c2 c3)) c1))
     (define temp (flsum (list a5 (fl* -1.0 c4) (fl* b1 a4))))
     (cond
       [(= temp 0.0)
        (list 0.0 0.0)]
       ;!!!if temp ≈ 0.0 these values blow up. Is this a good idea?
       [else
        (list (fl+ (fl* -1.0 (fl/ (fl+ (fl* u (fl+ c3 c2)) (fl* v (fl+ (fl* b1 a1)(fl* b2 a7)))) temp)) u)
              (fl* v (fl+ 1.0 (fl/ c4 temp))))])]))

(define (calcSC->nextK [qP : flpoly][K : flpoly]
                       [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : flpoly
  (match (calcSC K a b u v)
    [(list tFlag qk c+ud c d)
     (nextK qP qk tFlag a b 0.0 0.0 0.0)]
    [(list tFlag qk c+ud c d e f g h a1 a3 a7)
     (nextK qP qk tFlag a b a1 a3 a7)]))
(define (calcSC->newest [P : flpoly][K : flpoly]
                        [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (List TFlag Flonum Flonum)
  (match (calcSC K a b u v)
    [(list tFlag qk c+ud c d)
     (cons tFlag (newest P K tFlag a 0.0 0.0 0.0 b 0.0 0.0 0.0 0.0 0.0 u v))]
    [(list tFlag qk c+ud c d e f g h a1 a3 a7)
     (cons tFlag (newest P K tFlag a a1 a3 a7 b c d f g h u v))]))
(define (calcSC->K+newest [P : flpoly][qP : flpoly][K : flpoly]
                          [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (List flpoly TFlag Flonum Flonum)
  (define K+ (calcSC->nextK qP K a b u v))
  (cons K+ (calcSC->newest P K+ a b u v)))

; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT [maxiter : Integer]
                [P : flpoly][K : flpoly]
                [sss : Flonum])
  : (U (List 'RealIT:normal flpoly flpoly Flonum Flonum)
       (List 'RealIT:maxiter flpoly flpoly Flonum)
       (List 'RealIT:zero-cluster flpoly flpoly Flonum))
  (let loop ([j 1]
             [K K]
             [s sss][omp 0.0][t 0.0])
    ; Evaluate p at s and compute remainder
    (define-values (qP pv) (flpoly-reduce-root-QR P s))
    (define mp (abs pv))
    ;Compute a rigorous bound on the error in evaluating p
    (define ms (abs s))
    (define ee (+ (* (for/fold ([ee : Flonum (fl* 0.5 (flabs (flpoly-reverse-coefficient qP 0)))])
                               ([i : Integer (in-range 1 (+ 1 (flpoly-degree qP)))])
                       (fl+ (fl* ee ms) (flabs (flpoly-reverse-coefficient qP i))))
                     ms)
                  mp))
    (cond
      [(fl<= mp (fl* (fl* 20.0 epsilon.0) (fl- (fl* 2.0 ee) mp)))
       ;Iteration has converged sufficiently if the polynomial
       ;value is less than 20 times this bound
       (list 'RealIT:normal qP K sss s)]
      [(> j maxiter)
       (list 'RealIT:maxiter qP K sss)]
      [(and (>= j 2)
            (fl<= (abs t) (fl* 0.001 (flabs (- s t)))) (> mp omp))
       ;A cluster of zeros near the real axis has been encountered;
       ;Return with iFlag set to initiate a quadratic iteration
       (list 'RealIT:zero-cluster qP K s)]
      [else
       ;Return if the polynomial value has increased significantly
       ;Compute t, the next polynomial and the new iterate
       (define-values (qK kv)(flpoly-reduce-root-QR K s))
       ;Use the scaled form of the recurrence if the value of K at s is non-zero
       (define K+
         (if (fl> (flabs kv) (fl* (flabs (flpoly-coefficient K 0)) epsilon10))
             (flpoly+ (flpoly*s qK (- (/ pv kv))) qP)
             qK))
       (define kv+ (Horner K+ s))
       (define t+ (if (fl> (abs kv+) (fl* (flabs (flpoly-coefficient K+ 0)) epsilon10)) (fl* -1.0 (fl/ pv kv+)) 0.0))
       (loop (+ j 1) K+ (fl+ s t+) mp t+)])))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT [maxiter : Integer]
                [P : flpoly][K : flpoly]
                [uu : Flonum][vv : Flonum])
  : (List (U 0 2) flpoly flpoly Flonum Flonum Flonum Flonum)
  (let loop ([j 0][omp 0.0][relstp 0.0][tried? : Boolean #f]
             ;uu and vv are coefficients of the starting quadratic
             [u uu][v vv]
             [qp (flpoly> 0.0)][K K])
    (match-define (list (cons szr szi)(cons lzr lzi))(Quad (flpoly> 1. u v)))
    (cond
      [(> (abs (- (abs szr)(abs lzr))) (* 0.01 (abs lzr)))
       ;Return if the roots of the quadratic are real and not close
       ;to multiple or nearly equal and of opposite sign
       (list 0 qp K szr szi lzr lzi)]
      [else
       ;Evaluate polynomial by quadratic synthetic division
       (match-define (list qP a+ub a b)(QuadraticSyntheticDivision P u v))
       (define sP (flpoly+ (flpoly-shift qP 1) (flpoly> b)))
       (define mp (+ (abs (- a (* szr b))) (abs (* szi b))))
       ;Compute a rigorous bound on the rounding error in evaluating p
       (define zm (sqrt (abs v)))
       (define t (- (* szr b)))
       (define e0 (for/fold ([e0 : Flonum (fl* 2.0 (abs (flpoly-reverse-coefficient sP 0)))])
                                      ([i : Integer (in-range 1 (+ (flpoly-degree sP) 1))])
                              (fl+ (fl* e0 zm) (flabs (flpoly-reverse-coefficient sP i)))))
       (define ee (fl* (flsum (list (fl* 9.0 (fl+ (fl* e0 zm) (flabs (fl+ a t))))
                                    (fl* 2.0 (flabs t))
                                    (fl* -7.0 (fl+ (flabs (fl+ a t))(fl* zm (flabs b))))))
                     epsilon.0))
(println (list 'A j sP a b mp zm t e0 ee))
       (cond
         [(fl<= mp (fl* 20.0 ee))
          ;Iteration has converged sufficiently if the polynomial
          ;value is less than 20 times this bound
          (list 2 sP K szr szi lzr lzi)]
         ;Stop iteration after 20 steps
         [(> j maxiter)
          (list 0 sP K szr szi lzr lzi)]
         [else
          (define-values (j+ tried?+ u+ v+ a+ b+ sP+ K+)
            (cond
              [(and (>= j 2)
                    (fl<= relstp 0.01) (fl>= mp omp) (not tried?))
               ;A cluster appears to be stalling the convergence.
               ;Five fixed shift steps are taken with a u, v close to the cluster
               (define relstp+ (if (fl< relstp epsilon.0) (flsqrt epsilon.0) (flsqrt relstp)))
               (define u+ (fl- u (fl* u relstp+)))
               (define v+ (fl+ v (fl* v relstp+)))
               (match-define (list qP+ a+ub+ a+ b+)(QuadraticSyntheticDivision P u+ v+))
               (define sP+ (flpoly+ (flpoly-shift qP+ 1) (flpoly> b)))
               (define K+
                 (for/fold ([K+ : flpoly K])
                           ([i : Integer (in-range 5)])
                   (calcSC->nextK sP+ K+ a+ b+ u+ v+)))
               (values 0 #t u+ v+ a+ b+ sP+ K+)]
              [else
               (values j tried? u v a b sP K)]))
(println (list 'B j u+ v+ a+ b+ sP+ K+))
          ;Calculate next K polynomial and new u and v
          (match-define (list Ki _ ui vi)(calcSC->K+newest P sP+ K+ a+ b+ u+ v+))
(println (list 'C j Ki ui vi))
          (cond
            [(= vi 0.0)
             ;If vi is zero, the iteration is not converging
             (list 0 sP+ Ki szr szi lzr lzi)]
            [else
             (loop (+ j+ 1) mp (flabs (fl/ (fl- vi v+) vi)) tried?+
                   ui vi sP+ Ki)])])])))


(module* test racket/base
  (require rackunit
           math/flonum
           (submod "..")
           "../poly-flonum.rkt")
  (define bigmargin (* 1e4 epsilon.0))
  ;Quad
  (check-within (Quad (flpoly> 1. 0. 0.))  '((0.0 . 0.0)(-0.0 . 0.0)) epsilon10)
  (check-within (Quad (flpoly> 1. 0. 1.))  '((-0.0 . 1.0) (-0.0 . -1.0)) epsilon10)
  (check-within (Quad (flpoly> 1. 0. -1.)) '((-1.0 . 0.0) (1.0 . 0.0)) epsilon10)
  (check-within (Quad (flpoly> 1. 1. 0.))  '((0.0 . 0.0) (-1.0 . 0.0)) epsilon10)
  (check-within (Quad (flpoly> 1. 6. 3.))  '((-0.5505102572168219 . 0.0)  (-5.449489742783178 .  0.0)) epsilon10)
  (check-within (Quad (flpoly> 1. 2. 3.))  '((-1.0 . 1.414213562373095)   (-1.0 . -1.414213562373095)) epsilon10)
  (check-within (Quad (flpoly> 1. 6. 7.))  '((-1.585786437626905 . 0.0)   (-4.414213562373095 . 0.0)) epsilon10)
  (check-within (Quad (flpoly> +max.0 0.9 -min.0)) '((4.9406564584125e-324 . 0.0) (-5.00641618164121e-309 . 0.0)) epsilon10)
  (check-equal? (Quad (flpoly> +inf.0 1e10 -9e-303)) '((+nan.0 . 0.0) (+nan.0 . 0.0)) epsilon10)
  
  ;QuadraticSyntheticDivision
  (check-within (QuadraticSyntheticDivision (flpoly> 1. 2. 3. 4.) 2.8 3.5)
                (list (flpoly> 1.0 -0.8) (+ 1.928 (* 2.8 1.74)) 1.928 1.74)
                 epsilon10)
  (check-within (QuadraticSyntheticDivision (flpoly> 0.428 3.62 2.6e-4 12. 0.005) 3.345 6.482)
                (list (flpoly> 0.428 2.18834 -10.0940333)
                      (+ -40.199644595332494 (* 3.345 31.5797215085)) -40.199644595332494 31.5797215085)
                 bigmargin)

  ;calcSC
  (check-within (calcSC (flpoly> 1. 2. 3. 4.) 2.3 4.6 1.8 9.2)
                (list 'calcSC:div-by-c
                      (flpoly> 1.0 0.2)
                      2.16 13.968 -6.56 0.16466208476517755 -0.46964490263459335 0.2963917525773196 42.32
                      5.680183276059564 15.679123711340203 -19.519702176403204)
                epsilon100)
  (check-within (calcSC (flpoly> 1. -10. 35. -50.) 2.3 4.6 -6. 8.)
                (list 'calcSC:div-by-d
                      (flpoly> 1.0 -4.0)
                      -18.0 0.0 3.0 0.7666666666666666 0.0 -27.6 36.8
                      -2.3 37.03 23.0)
                epsilon100)
  (check-within (calcSC (flpoly> 1. -10. 35. -50. 24.) 2.3 4.6 -6. 8.00000000000001)
                (list 'calcSC:almost-factor
                      (flpoly> 1.0 -4.0 2.999999999999986)
                      5.3290705182007514e-14 -1.7408297026122455e-13 -4.263256414560601e-14)
                bigmargin)

  ;nextK
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:div-by-c 8. 9. 10. 6. 7.)
                (flpoly> 16.0 5.8 12.7 13.6)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:div-by-c 8. 9. 0. 6. 7.)
                (flpoly> 0. -112. -53. -54.)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:almost-factor 8. 9. 10. 6. 7.)
                (flpoly> 0. 0. 11. 12.)
                epsilon100)

  ;newest
  (check-within (newest (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:almost-factor 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (newest (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-d 1. 5. -0.8908220965637230 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (newest (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-d 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(11.239868703446534 12.148466102764804) epsilon100)
  (check-within (newest (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-c 1. 5. 100.52892561983471 0. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (newest (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-c 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(11.047985250849212 12.029700344736144) epsilon100)
  (check-within (newest (flpoly> 765.85527498437887 -1347.293632350993 -2161.1901804835061 -7837.7065086597486 -3083.5325907341339 2512.6246767498906 5888.8148218838123 -224.71114833786896 4321.6465771244393 -4104.5415694069588 -358.02596267509489 -5940.1714091583599 -2813.1556404590783 -1218.7896752219331 -92.316085769292613 13.465814510071247 )
                        (flpoly> 765.85527498437887 569.21989433594013 -70.015121432447586 -702.31273591596982 -9385.9870113488287 7161.0962876975536 -6.3514328002929688 2149.7078857421875 2603.109375 -6064. -80480. 4108288. 128712704. -11601444864. -569620037632.)
                        'calcSC:div-by-c 4.2070203373260126e+029 -5.2749842363542267e+027 -5.5170988810118383e+027 -9.7406057385308503e+025 0.017655303899038365 -539.9094138852181 -1.9916002499454986e+031 7.080387980931846 3775.5567802833493
                         -1.2702606492846791e+028 -4.8274289306750895e+031 1.2166940450248765e+029)
                '(3.7978598044219325e-10 -5.868394095550277e-11) epsilon100)

  ;RealIT
  (check-within (RealIT 10 (flpoly> 1. 2. 3. 4. -5.) (flpoly> 1. 2. 3. 4.) 0.2)
                (list 'RealIT:normal
                      (flpoly> 1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                      (flpoly> 1.0 2.6841243194530695 4.836274723373265 7.308613153815818)
                      0.2 0.6841243194530697)
                epsilon100)
  (check-within (RealIT 10 (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) 1.0)
                (list 'RealIT:maxiter
                      (flpoly> 1.0 -0.6849750434472566 4.839140897040084 -8.992972540277597)
                      (flpoly> 1.0 1.0919036572997787 1.0019196569203022 3.933013624211993)
                      1.0)
                epsilon100)
  (check-within (RealIT 10 (flpoly> 4.9679877220982345 9.29937913880471 -9.609506455896735 -2.5160214731778163 -6.029809381393797)
                        (flpoly> 8.514417957281449 0.5198895391395837 -9.66980775616132 0.45524621258751097) 3.5502909446276085)
                (list 'RealIT:zero-cluster
                      (flpoly> 4.9679877220982345 2.2034324874736058 -12.756744383111027 15.70487250861968)
                      (flpoly> 4.9679877220982345 -6701.697712994184 7942.889509061441 -1976.5039946730667)
                      -1.4283341763844224)
                epsilon100)
  (check-within (RealIT 10 (flpoly> 1. 2. 3. 4. -5.) (flpoly> 1. 2. 3. 0.) 0.0)
                (list 'RealIT:normal
                      (flpoly> 1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                      (flpoly> 1.0 2.6841243194530113 4.836274723373138 7.308613153815954)
                      0.0 0.6841243194530697)
                epsilon100)

  ;QuadIT
  (check-within (QuadIT 20 (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) 6. 7.)
                (list 0 (flpoly> 0.0 0.0 0.0 0.0 0.0)
                      (flpoly> 1. 2. 3. 4.)
                      -1.585786437626905 0 -4.414213562373095 0) epsilon100)
  ;QuadIT-converged
  (check-within (QuadIT 20 (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) -0.575630959115296 0.0828377502729989)
                (list 2 (flpoly> 1.0 2.575630959115296 2.3944555573388273 0. 0.)
                      (flpoly> 1.0 2.7141314657388516 2.7511817500546467 0.3316333077843976)
                      0.287815479557648 1.4160930801719076 0.287815479557648 -1.4160930801719076) epsilon100)
  ;QuadIT-maxiter
  ;[TODO ???]
  ;QuadIT-relstp
  (check-within (QuadIT 20
                        (flpoly> -74.43388870038298 -48.684338183687615 82.95039531162064 2.082613677062014 60.82122424869209 -46.15017147716964 61.0180453610964 47.02754709444238 -5.330451975747479 91.51704177156668)
                        (flpoly> 38.515673952936254 7.252656554000609 -84.42246656861926 31.693388752691646 -27.265410421231138 -35.244767584584565 -97.79006609235279 8.92096535665003 -60.693225828975194)
                         14.737906787890154 56.6995805579966)
                (list 2 (flpoly> -74.43388870038298    28.5525675415266  134.72025177002524 -168.93474867929848   88.79349933216068  46.45222659669343 -84.28416458872897   83.6875414818494   -4.263256414560601e-14 0.0)
                      (flpoly> -74.43388870038298 -1291.101631406862   640.9347772344079  2219.5491668571904 -2906.28648822974   1620.6910078684268  739.2772124821581 -1410.6042877693205 1483.7141716555477)
                      -0.5188289035664532 0.907949839624714 -0.5188289035664532 -0.907949839624714)
                epsilon100)
  ;QuadIT-nonconverging
  (check-within (QuadIT 20
                        (flpoly> 765.8552749843789 -1347.293632350993 -2161.190180483506 -7837.706508659749 -3083.532590734134 2512.6246767498906 5888.814821883812 -224.71114833786896 4321.646577124439 -4104.541569406959 -358.0259626750949 -5940.17140915836 -2813.1556404590783 -1218.789675221933 -92.31608576929261 13.465814510071247)
                        (flpoly> 569.9471955954955 426.1973931512889 -39.26465304820874 -525.558286377151 -6935.288424258491 5283.823600793081 -1.6306656043934709 1584.535288608834 1907.3886808609604 -3739.1601002469033 -430.3641207148028 3278.5379900289245 -1171.8752324055004 1657.6923655682594 -2854.6807003064246)
                        7.080387980931846 3775.5567802833493)
                (list 0 (flpoly> 765.8552749843789 -1347.2936322007815 -2161.190180771193 -7837.7065090424085 -3083.5325922052557 2512.62467638493 5888.814822470982 -224.71114725974803 4321.646576900171 -4104.541568552454 -358.0259636123816 -5940.171409102984 -2813.1556416132016 -1218.7896755919267 -92.31608592225949 13.465814529259115)
                      (flpoly> 765.8552749843789 -1235.5810851818474 -2357.715044087775 -8152.951526701866 -4226.790575157413 2062.8408974624554 6255.322322625176 634.2690337473058 4288.868772236702 -3474.158567758887 -956.7406398036304 -5992.395365236808 -3679.6270225980984 -1629.1345512998803 -270.0965405173288)
                      9.806777612197948e-11 5.531679987906852e-06 9.806777612197948e-11 -5.531679987906852e-06)
                epsilon100)
  ;QuadIT-normal [done in break converged]
)
