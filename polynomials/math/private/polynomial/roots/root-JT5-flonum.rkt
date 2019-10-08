#lang typed/racket/base

(require math/flonum
         racket/math)
(require "../poly-flonum.rkt"
         "root-bounds.rkt")

(provide (all-defined-out))

(define (pp [P : flpoly]#:type [t : Symbol '>]) : (U flpoly String (Listof Any))
  (case t
    [(>)(cons 'flpoly> (for/list : (Listof Flonum)([i : Integer (in-range (+ (flpoly-degree P) 1))])(flpoly-reverse-coefficient P i)))]
    [(<)(cons 'flpoly< (for/list : (Listof Flonum)([i : Integer (in-range (+ (flpoly-degree P) 1))])(flpoly-coefficient P i)))]
    [(x)(apply string-append (for/list : (Listof String) ([i : Integer (in-range (flpoly-degree P) -1 -1)])(format "~ax^~a~a" (flpoly-coefficient P i) i (if (= i 0) "" "+"))))]
    [else P]))

(require syntax/location)
(define-syntax-rule (label x)(println (quote-srcloc x)))

(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))

(struct iteration-scheme ([ZeroShift : Nonnegative-Integer][1Root : Nonnegative-Integer][Multiplier : Nonnegative-Integer][FixedShift : Nonnegative-Integer][QuadShift : Nonnegative-Integer][QuadFixedShift : Nonnegative-Integer][LinShift : Nonnegative-Integer]))
(define (make-iteration-scheme #:zero-shift [ZeroShift : Nonnegative-Integer 5]
                               #:1root [1Root : Nonnegative-Integer 20]
                               #:multiplier [Multiplier : Nonnegative-Integer 20]
                               #:quad-shift [QuadShift : Nonnegative-Integer 20]
                               #:quad-fixed-shift [QuadFixedShift : Nonnegative-Integer 5]
                               #:linear-shift [LinShift : Nonnegative-Integer 10])
  : iteration-scheme
  (iteration-scheme ZeroShift 1Root Multiplier 0 QuadShift QuadFixedShift LinShift))

(define-type TFlag (U 'calcSC:almost-factor 'calcSC:div-by-c 'calcSC:div-by-d))

(define RADFAC (/ pi 180));Degrees - to - radians conversion factor = pi/180
(define rotator (make-polar 1 (* 94 RADFAC)))


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
(define (Quad [P : flpoly]) :  (Values Flonum Flonum Flonum Flonum)
  (unless (= (flpoly-degree P) 2) (raise-argument-error 'Quad "not a quadratic" P))
  (define a0 (flpoly-coefficient P 0))
  (define a1 (flpoly-coefficient P 1))
  (define a2 (flpoly-coefficient P 2))
  (cond
    [(= a0 0)(label x) (values 0.0 0.0 (fl* -1.0 (fl/ a1 a2)) 0.0)]
    ;what if a2/a1/a0 ±inf.0
    [else
     (define a1/2 (fl/ a1 2.0))
     (define-values (D* E*)
       (cond
           [(fl< (flabs a1/2) (flabs a0))
            (define E0
              (cond
                [(fl< a0 0.0) (fl* -1.0 a2)]
                [else         a2]))
            (define E1 (fl- (fl* a1/2 (fl/ a1/2 (flabs a0))) E0))
            (values (fl* (flsqrt (flabs E1)) (flsqrt (flabs a0)))
                    E1)]
           [else
            (define E
              (let ([E (fl- 1.0 (fl* (fl/ a2 a1/2)(fl/ a0 a1/2)))])
                (cond
                  [(not (or (nan? E)(infinite? E))) E]
                  [else(label x) (fl- 1.0 (fl/ (fl/ (fl* a2 a0) a1/2) a1/2))])))
            (values (fl* (flsqrt (flabs E))(flabs a1/2))
                    E)]))
     ;compute Discriminant avoiding overflow
     (cond
       [(< E* 0)
        ;conjugate zeros
        (define R (- (/ a1/2 a2)))
        (define I (abs (/ D* a2)))
        (values R I R (- I))]
       [else
        ;real zeros
        (define D** (cond [(> a1/2 0) (- D*)][else D*]))
        (define Z1 (/ (- D** a1/2) a2))
        (cond
          [(= Z1 0) (label x)(values 0.0 0.0 0.0 0.0)]
          [else     (values (/ (/ a0 Z1) a2) 0.0 Z1 0.0)])])]))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision [P : flpoly][u : Flonum][v : Flonum])
  (define-values (qP rP)(flpoly/p-QR P (flpoly> 1.0 u v)))
  (values qP
          (flpoly-coefficient rP 0)
          (fl- (flpoly-coefficient rP 0)(fl* u (flpoly-coefficient rP 1)))
          (flpoly-coefficient rP 1)))

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
;struct used for answers because match is too stupid for typed/racket
(define (calcSC [K : flpoly][a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (Values TFlag flpoly Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum Flonum)
  ;Synthetic division of K by the quadratic 1, u, v
  (define-values (qK c+ud c d)(QuadraticSyntheticDivision K u v))
  (cond
    [(and (fl<= (flabs c) (* epsilon100 (flabs (flpoly-coefficient K 0))))
          (fl<= (flabs d) (* epsilon100 (flabs (flpoly-coefficient K 1)))))
     ;type=3 indicates the quadratic is almost a factor of K
     (values 'calcSC:almost-factor qK c+ud c d 0.0 0.0 0.0 0.0 0.0 0.0 0.0)]
    [else
     (define bv (fl* v b))
     (cond
       [(fl>= (flabs d) (flabs c))
        ;TYPE = 2 indicates that all formulas are divided by d
        (define a/d (fl/ a d))
        (define c/d (fl/ c d))
        (define bu (fl* u b))
        (define a1 (fl- (fl* c/d b) a));bc/d-a~>bc-ad
        (define a3 (fl+ (fl* a/d (+ bu a)) (fl* bv (/ b d))));aa/d+abu/d+bbv/d~>aa+abu+bbv
        (define a7 (fl+ bv (fl* c+ud a/d)));bv+ac/d+adu/d~>bvd+ac+adu
        (values 'calcSC:div-by-d qK c+ud c d a/d c/d bu bv a1 a3 a7)]
       [else
        ;TYPE = 1 indicates that all formulas are divided by c
        (define a/c (fl/ a c))
        (define d/c (fl/ d c))
        (define au/c (fl* a/c u))
        (define a1 (fl- b (fl* a d/c)));b-ad/c~>bc-ad
        (define a3 (fl+ (fl* a/c a) (fl* (fl+ au/c (fl/ bv c)) b)));aa/c+abu/c+bbv/c~>aa+abu+bbv : aa+b(ua+vb)
        (define a7 (fl+ (fl* bv d/c) (fl* c+ud a/c)));bvd/c+ac/c+adu/c~>bvd+ac+adu : ac+d(ua+vb)
        (values 'calcSC:div-by-c qK c+ud c d a/c d/c au/c bv a1 a3 a7)])]))

;Computes the next K polynomials using the scalars computed in calcSC
(define (nextK [qP : flpoly][qK : flpoly]
               [tFlag : TFlag]
               [a : Flonum][b : Flonum][a1 : Flonum][a3 : Flonum][a7 : Flonum])
  : flpoly
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     ; use unscaled form of the recurrence
     qK]
    [else
     (define temp (if (equal? tFlag 'calcSC:div-by-c) b a))
     (cond
       [(fl> (flabs a1) (fl* epsilon10 (abs temp)))
        (define a7+ (fl/ a7 a1))
        (define a3+ (fl/ a3 a1))
        (flpoly+ (flpoly*p qP (flpoly> 1.0 (- a7+)))
                 (flpoly*s qK a3+)
                 (const-flpoly b))]
       [else
        (label x)
        (flpoly+ (flpoly*s qP (- a7))
                 (flpoly*s qK a3))])]))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest [P : flpoly][K : flpoly]
                [tFlag : TFlag]
                [a : Flonum][b : Flonum][c : Flonum][d : Flonum][f : Flonum][g : Flonum][h : Flonum][u : Flonum][v : Flonum]
                [a1 : Flonum][a3 : Flonum][a7 : Flonum])
  : (Values Flonum Flonum)
  (cond
    [(equal? tFlag 'calcSC:almost-factor) (values 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (cond
         [(equal? tFlag 'calcSC:div-by-c)
          (values (flsum (list a (fl* u b) (fl* h f)));a+ub+vbd/c~>ac+ubc+vbd
                  (fl+ c (fl* (fl+ u (fl* v f)) d)))];c+du+dvd/c~>cc+cdu+dvd
         [else
          (values (fl+ (fl* (fl+ a g) f) h);ac/d+buc/d+bv~>ac+ubc+bvd
                  (fl+ (fl* (fl+ f u) c) (fl* v d)))]));cc/d+uc+vd~>cc+ucd+vdd

     (define b1 (fl* -1.0 (fl/ (flpoly-coefficient K 0)(flpoly-coefficient P 0))))
     (define b2 (fl* -1.0 (fl/ (fl+ (flpoly-coefficient K 1) (fl* b1 (flpoly-coefficient P 1))) (flpoly-coefficient P 0))))
     (define c1 (fl* (fl* v b2) a1))
     (define c2 (fl* b1 a7))
     (define c3 (fl* (fl* b1 b1) a3))
     (define c4 (fl+ (fl* -1.0 (fl+ c2 c3)) c1))
     (define temp (flsum (list a5 (fl* -1.0 c4) (fl* b1 a4))))
     (cond
       [(= temp 0.0) (values 0.0 0.0)]
       ;!!!if temp ≈ 0.0 these values blow up. Is this a good idea?
       [else
        (values (fl+ (fl* -1.0 (fl/ (fl+ (fl* u (fl+ c3 c2)) (fl* v (fl+ (fl* b1 a1)(fl* b2 a7)))) temp)) u)
                (fl* v (fl+ 1.0 (fl/ c4 temp))))])]))

(define (calcSC->nextK [qP : flpoly][K : flpoly]
                       [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : flpoly
  (define-values (tFlag qK c+ud c d e f g h a1 a3 a7)(calcSC K a b u v))
  (case tFlag
    [(calcSC:almost-factor)
     (nextK qP qK
            tFlag a b 0.0 0.0 0.0)]
    [else
     (nextK qP qK tFlag a b a1 a3 a7)]))
(define (calcSC->newest [P : flpoly][K : flpoly]
                        [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (values TFlag Flonum Flonum)
  (define-values (tFlag qK c+ud c d e f g h a1 a3 a7)(calcSC K a b u v))
  (case tFlag
    [(calcSC:almost-factor)
     (define-values (u+ v+)(newest P K tFlag a b 0.0 0.0 0.0 0.0 0.0 u v 0.0 0.0 0.0))
     (values tFlag u+ v+)]
    [else
     (define-values (u+ v+)(newest P K tFlag a b c d f g h u v a1 a3 a7))
     (values tFlag u+ v+)]))
(define (calcSC->K+newest [P : flpoly][qP : flpoly][K : flpoly]
                          [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : (values TFlag flpoly Flonum Flonum)
  (define K+ (calcSC->nextK qP K a b u v))
  (define-values (tFlag u+ v+)(calcSC->newest P K+ a b u v))
  (values tFlag K+ u+ v+))

(define (altabs-Horner [qP : flpoly][f : Flonum][s : Flonum][p : Flonum]) : Flonum
  (fl+ (for/fold ([ee : Flonum (fl* f (flabs (flpoly-reverse-coefficient qP 0)))])
                 ([i : Integer (in-range 1 (+ (flpoly-degree qP) 2))])
         (fl+ (fl* ee s) (flabs (flpoly-reverse-coefficient qP i))))
       p))

; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT [IS : iteration-scheme]
                [P : flpoly][K : flpoly]
                [sss : Flonum])
  : (Values (U 'RealIT:normal 'RealIT:zero-cluster 'RealIT:maxiter)
            flpoly Flonum)
  (let loop ([j 1]
             [K K]
             [s sss][absP@s_old 0.0][t 0.0])
    ; Evaluate p at s and compute remainder
    (define-values (qP P@s) (flpoly-reduce-root-QR P s))
    (define absP@s (abs P@s))
    ;Compute a rigorous bound on the error in evaluating p
    (define ee (altabs-Horner qP 0.5 (abs s) absP@s))
    (cond
      [(fl<= absP@s (fl* (fl* 20.0 epsilon.0) (fl- (fl* 2.0 ee) absP@s)))
       ;Iteration has converged sufficiently if the polynomial
       ;value is less than 20 times this bound
       (values 'RealIT:normal qP s)]
      [(> j (iteration-scheme-LinShift IS))
       (values 'RealIT:maxiter flpoly-zero 0.0)]
      [(and (>= j 2)
            (fl<= (abs t) (fl* 0.001 (flabs (- s t)))) (> absP@s absP@s_old))
       ;A cluster of zeros near the real axis has been encountered;
       ;Return with iFlag set to initiate a quadratic iteration
       (values 'RealIT:zero-cluster K s)]
      [else
       ;Return if the polynomial value has increased significantly
       ;Compute t, the next polynomial and the new iterate
       (define-values (qK K@s)(flpoly-reduce-root-QR K s))
       ;Use the scaled form of the recurrence if the value of K at s is non-zero
       (define K+
         (if (fl> (flabs K@s) (fl* (flabs (flpoly-coefficient K 0)) epsilon10))
             (flpoly+ (flpoly*s qK (- (/ P@s K@s))) qP)
             qK))
       (define kv+ (Horner K+ s))
       (define t+ (if (fl> (abs kv+) (fl* (flabs (flpoly-coefficient K+ 0)) epsilon10)) (fl* -1.0 (fl/ P@s kv+)) 0.0))
       (loop (+ j 1) K+ (fl+ s t+) absP@s t+)])))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT [IS : iteration-scheme]
                [P : flpoly][K : flpoly]
                [uu : Flonum][vv : Flonum])
  : (Values (U 'QuadIT:maxiter 'QuadIT:nonquad 'QuadIT:nonconverging 'QuadIT:normal)
            flpoly Number Number)
  (let loop ([j 0][omp 0.0][relstp 0.0][tried? : Boolean #f]
             ;uu and vv are coefficients of the starting quadratic
             [u uu][v vv][K K])
    (define-values (szr szi lzr lzi)(Quad (flpoly> 1. u v)))
    (cond
      [(> (abs (- (abs szr)(abs lzr))) (* 0.01 (abs lzr)))
       ;Return if the roots of the quadratic are real and not close
       ;to multiple or nearly equal and of opposite sign
       (values 'QuadIT:nonquad flpoly-zero 0 0)]
      [else
       ;Evaluate polynomial by quadratic synthetic division
       (define-values (qP a+ub a b)(QuadraticSyntheticDivision P u v))
       (define mp (+ (abs (- a (* szr b))) (abs (* szi b))))
       ;Compute a rigorous bound on the rounding error in evaluating p
       (define zm (sqrt (abs v)))
       (define t (- (* szr b)))
       (define e0 (altabs-Horner qP 2.0 zm b))
       (define ee (fl* (flsum (list (fl* 9.0 (fl+ (fl* e0 zm) (flabs (fl+ a t))))
                                    (fl* 2.0 (flabs t))
                                    (fl* -7.0 (fl+ (flabs (fl+ a t))(fl* zm (flabs b))))))
                       epsilon.0))
       (cond
         [(fl<= mp (fl* 20.0 ee))
          ;Iteration has converged sufficiently if the polynomial
          ;value is less than 20 times this bound
          (values 'QuadIT:normal qP (+ szr (* +i szi)) (+ lzr (* +i lzi)))]
         ;Stop iteration after 20 steps
         [(> j (iteration-scheme-QuadShift IS))
          (values 'QuadIT:maxiter flpoly-zero 0 0)]
         [else
          (define-values (j+ tried?+ u+ v+ a+ b+ qP+ K+)
            (cond
              [(and (>= j 2)
                    (fl<= relstp 0.01) (fl>= mp omp) (not tried?))
               ;A cluster appears to be stalling the convergence.
               ;Five fixed shift steps are taken with a u, v close to the cluster
               (define relstp+ (if (fl< relstp epsilon.0) (flsqrt epsilon.0) (flsqrt relstp)))
               (define u+ (fl- u (fl* u relstp+)))
               (define v+ (fl+ v (fl* v relstp+)))
               (define-values (qP+ a+ub+ a+ b+)(QuadraticSyntheticDivision P u+ v+))
               (define K+
                 (for/fold ([K+ : flpoly K])
                           ([i : Integer (in-range (iteration-scheme-QuadFixedShift IS))])
                   (calcSC->nextK qP+ K+ a+ b+ u+ v+)))
               (values 0 #t u+ v+ a+ b+ qP+ K+)]
              [else
               (values j tried? u v a b qP K)]))
          ;Calculate next K polynomial and new u and v
          (define-values (tFlag Ki ui vi)(calcSC->K+newest P qP+ K+ a+ b+ u+ v+))
          (cond
            [(fl= vi 0.0)
             ;If vi is zero, the iteration is not converging
             (values 'QuadIT:nonconverging flpoly-zero 0 0)]
            [else
             (loop (+ j+ 1) mp (flabs (fl/ (fl- vi v+) vi)) tried?+
                   ui vi Ki)])])])))

(define (tryQuad [IS : iteration-scheme][P : flpoly][K : flpoly]
                 [sss : Flonum][ui : Flonum][vi : Flonum]
                 [quadConvergingLimit : Flonum][linConvergingLimit : Flonum]
                 [next : (-> flpoly Flonum Flonum (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number)))]
                 [tryLin? : Boolean])
  : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
  (define-values (qFlag qP sz lz)(QuadIT IS P K ui vi))
  ;decrease the convergence criterion for if Quadratic iteration fails, 
  (define  qCL (fl* quadConvergingLimit 0.25))
  (cond
    [(equal? qFlag 'QuadIT:normal) (values 'FixedShift:normal qP (list sz lz))]
    [tryLin?                       (tryLin IS P K sss ui vi qCL linConvergingLimit next #f)]
    [else                          (next K qCL linConvergingLimit)]))
(define (tryLin [IS : iteration-scheme][P : flpoly][K : flpoly]
                [sss : Flonum][ui : Flonum][vi : Flonum]
                [quadConvergingLimit : Flonum][linConvergingLimit : Flonum]
                [next : (-> flpoly Flonum Flonum (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number)))]
                [tryQuad? : Boolean])
  : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
  (define-values (iFlag F z)(RealIT IS P K sss))
  ;decrease the convergence criterion for if Linear iteration fails, 
  (define lCL (fl* linConvergingLimit 0.25))
  (cond
    [(equal? iFlag 'RealIT:normal)       (values 'FixedShift:normal F (list z))]
     ;If linear iteration signals an almost double real zero, attempt quadratic iteration
    [(equal? iFlag 'RealIT:zero-cluster) (tryQuad IS P F sss (fl* -2.0 z) (fl* z z) quadConvergingLimit lCL next #f)]
    [tryQuad?                            (tryQuad IS P K sss ui vi quadConvergingLimit lCL next #f)]
    [else                                (next K quadConvergingLimit lCL)]))

;The fixed shift
(define (FixedShift [IS : iteration-scheme]
                    [P : flpoly][K : flpoly]
                    [sr : Flonum][bnd : Flonum])
  : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
  (define u (* -2 sr))
  (define v bnd)
  ;Evaluate polynomial by synthetic division
  (define-values (qP a+ub a b)(QuadraticSyntheticDivision P u v))
  ;fixed shifts: do a fixed shift, if quadratic or linear convergence is detected try to start stage 3.
  ;If unsuccessful continue the fixed shifts
  (let loop ([j : Integer 0][K_old : flpoly K]
             [vv_old : Flonum v][ss_old : Flonum sr][tv_old : Flonum 0.0][ts_old : Flonum 0.0]
             [quadConvergingLimit : Flonum 0.25][linConvergingLimit : Flonum 0.25])
    (cond
      [(<= (iteration-scheme-FixedShift IS) j) (values 'FixedShift:maxiter flpoly-zero '())]
      [else
       ;Calculate next K polynomial and estimate vv
       (define-values (tFlag K uu vv)(calcSC->K+newest P qP K_old a b u v))
       ;Estimate s
       (define ss (if (fl= (flpoly-coefficient K 0) 0.0)
                      0.0
                      (fl* -1.0 (fl/ (flpoly-coefficient P 0)(flpoly-coefficient K 0)))))
       (cond
         [(or (= j 0) (equal? tFlag 'calcSC:almost-factor))
          (loop (+ j 1) K vv ss 1.0 1.0 quadConvergingLimit linConvergingLimit)]
         [else
          ; Compute relative measures of convergence of s and v sequences
          (define tv (if (not (fl= vv 0.0)) (flabs (fl/ (fl- vv vv_old) vv)) 1.0))
          (define ts (if (not (fl= ss 0.0)) (flabs (fl/ (fl- ss ss_old) ss)) 1.0))
          ;If decreasing, multiply the two most recent convergence measures
          (define tvv (if (fl< tv tv_old) (fl* tv tv_old) 1.0))
          (define tss (if (fl< ts ts_old) (fl* ts ts_old) 1.0))
          ;Compare with convergence criteria
          (define quadConverging? (fl< tvv quadConvergingLimit))
          (define linConverging? (fl< tss linConvergingLimit))
          (define (next [K : flpoly][quadConvergingLimit : Flonum][linConvergingLimit : Flonum])
            : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
            (loop (+ j 1) K vv ss tv ts quadConvergingLimit linConvergingLimit))
          (cond
            [(or linConverging? quadConverging?)
             ;At least one sequence has passed the convergence test.
             ;Choose iteration according to the fastest converging sequence, if it fails try the other one (if it is converging)
             (cond
               [(and linConverging? (or (not quadConverging?) (< tss tvv)))
                (tryLin IS P K ss uu vv quadConvergingLimit linConvergingLimit next quadConverging?)]
               [else
                (tryQuad IS P K ss uu vv quadConvergingLimit linConvergingLimit next linConverging?)])]
            [else
             (loop (+ j 1) K vv ss tv ts quadConvergingLimit linConvergingLimit)])])])))

;ZeroShift
(define (ZeroShift [maxiter : Integer][P : flpoly][K : flpoly])
  (define p0 (flpoly-coefficient P 0))
  (define p1 (flpoly-coefficient P 1))
  (for/fold  ([K : flpoly K])
             ([iter : Integer (in-range maxiter)])
    (define k0 (flpoly-coefficient K 0))
    (cond
      [(<= (abs k0) (* (abs p1) epsilon10)) ;Use unscaled form of recurrence
       ;in original zerok depends on scaling form: <= is for scaled, otherwise only if K[0]=0
       (flpoly-shift K -1)]
      [else ;Use scaled form of recurrence if value of K at 0 is nonzero
       (flpoly-shift (flpoly+ P (flpoly*s K (- (/ p0 k0)))) -1)])))

(define (1root [IS : iteration-scheme][P : flpoly][angle : Number])
  : (Values (U '1root:maxiter '1root:normal) flpoly Number (Listof Number))
  (define N (flpoly-degree P))
  ;Find the largest and smallest moduli of the coefficients
  (define P+ (flpoly*s P (flpoly-bestscale P)))
  ;Compute lower bound on moduli of zeros
  (define bnd (roots-mod-lower-bound P))
  ;Compute the (scaled) derivative as the initial K polynomial => K = p'/N
  (define K_0 (flpoly*s (flpoly-diff P) (/ 1. N)))
  ;do 5 steps with no shift
  (define K_1 (ZeroShift (iteration-scheme-ZeroShift IS) P+ K_0))
  ;Loop to select the quadratic corresponding to each new shift
  (let loop ([j : Nonnegative-Integer 0][angle : Number angle])
    (cond
      [(< j (iteration-scheme-1Root IS))
       ;Quadratic corresponds to a double shift to a non-real point and its
       ;complex conjugate. The point has modulus BND and angle rotated
       ;by 94° from the previous shift
       (define angle+ (* angle rotator))
       (define sr (* bnd (fl (real-part angle+))))
       ;The second stage jumps directly to one of the third stage iterations and returns here.
       (define-values (fFlag qP roots)
         (FixedShift (struct-copy iteration-scheme IS [FixedShift (* (+ j 1) (iteration-scheme-Multiplier IS))])
                     P+ K_1 sr bnd))
       (case fFlag
         ;successful, return the deflated polynomial and zero(s)
         [(FixedShift:normal) (values '1root:normal qP angle+ roots)]
         ;If the iteration is unseccessful, another quadratic is chosen after restoring K
         [else (loop (+ j 1) angle+)])]
      [else (values '1root:maxiter flpoly-zero angle '())])))

(define (roots [P : flpoly] #:iteration-scheme [IS : iteration-scheme (make-iteration-scheme)])
  : (Values (U 'roots:degree<1 'roots:maxiter 'roots:normal) (Listof Number))
  (cond
    [(< (flpoly-degree P) 1) (values 'roots:degree<1 '())]
    [else
     ;Remove zeros at the origin, if any
     (define s@0 (for/sum : Integer ([i : Integer (in-range (flpoly-degree P))]
                                     #:break (not (= 0 (flpoly-coefficient P i))))
                   1))

     ;Main loop
     (let loop ([P : flpoly (flpoly-shift P (- s@0))]
                [angle : Number (make-polar 1 (* -45 RADFAC))]
                [ans : (Listof Number) (for/list ([i (in-range s@0)]) 0.0)])
       (cond
         [(= (flpoly-degree P) 0) (values 'roots:normal ans)]
         [(= (flpoly-degree P) 1)
          (values 'roots:normal
                  `(,@ans ,(- (/ (flpoly-coefficient P 0) (flpoly-coefficient P 1)))))]
         [(= (flpoly-degree P) 2)
          (define-values (szr szi lzr lzi)(Quad P))
          (values 'roots:normal `(,@ans ,(+ szr (* +i szi)) ,(+ lzr (* +i lzi))))]
         [else
          (define-values (1flag qP angle+ roots) (1root IS P angle))
          (case 1flag
            [(1root:normal)
             (loop qP angle+ (append ans roots))]
            [(1root:maxiter)
             (values 'roots:maxiter '())])]))]))

(module* test racket/base
  (require rackunit
           math/flonum
           (submod "..")
           "../poly-flonum.rkt"
           (only-in "root-bounds.rkt" abs-coefficient-interval))
  (define (bigmargin n) (* (expt 10 n) epsilon100))
#|
  ;Quad
  (define (QL S2)(define-values (szr szi slr sli)(Quad S2))(list (cons szr szi)(cons slr sli)))
  (check-within (QL (flpoly> 1. 0. 0.))  '((0.0 . 0.0)(-0.0 . 0.0)) epsilon10)
  (check-within (QL (flpoly> 1. 0. 1.))  '((-0.0 . 1.0) (-0.0 . -1.0)) epsilon10)
  (check-within (QL (flpoly> 1. 0. -1.)) '((-1.0 . 0.0) (1.0 . 0.0)) epsilon10)
  (check-within (QL (flpoly> 1. 1. 0.))  '((0.0 . 0.0) (-1.0 . 0.0)) epsilon10)
  (check-within (QL (flpoly> 1. 6. 3.))  '((-0.5505102572168219 . 0.0)  (-5.449489742783178 .  0.0)) epsilon10)
  (check-within (QL (flpoly> 1. 2. 3.))  '((-1.0 . 1.414213562373095)   (-1.0 . -1.414213562373095)) epsilon10)
  (check-within (QL (flpoly> 1. 6. 7.))  '((-1.585786437626905 . 0.0)   (-4.414213562373095 . 0.0)) epsilon10)
  (check-within (QL (flpoly> +max.0 0.9 -min.0)) '((4.9406564584125e-324 . 0.0) (-5.00641618164121e-309 . 0.0)) epsilon10)
  (check-equal? (QL (flpoly> +inf.0 1e10 -9e-303)) '((+nan.0 . 0.0) (+nan.0 . 0.0)) epsilon10)
  
  ;QuadraticSyntheticDivision
  (define (QSDL P u v)
    (define-values (qP a+ub a b)(QuadraticSyntheticDivision P u v))
    (list qP a+ub a b))
  (check-within (QSDL (flpoly> 1. 2. 3. 4.) 2.8 3.5)
                (list (flpoly> 1.0 -0.8) (+ 1.928 (* 2.8 1.74)) 1.928 1.74)
                epsilon10)
  (check-within (QSDL (flpoly> 0.428 3.62 2.6e-4 12. 0.005) 3.345 6.482)
                (list (flpoly> 0.428 2.18834 -10.0940333)
                      (+ -40.199644595332494 (* 3.345 31.5797215085)) -40.199644595332494 31.5797215085)
                (bigmargin 1))

  ;calcSC
  (define (CSCL K a b u v)
    (define-values (tFlag qK c+ud c d e f g h a1 a3 a7)(calcSC K a b u v))
    (case tFlag
      [(calcSC:almost-factor)(list tFlag qK c+ud c d)]
      [else (list tFlag qK c+ud c d e f g h a1 a3 a7)]))
  (check-within (CSCL (flpoly> 1. 2. 3. 4.) 2.3 4.6 1.8 9.2)
                (list 'calcSC:div-by-c
                      (flpoly> 1.0 0.2)
                      2.16 13.968 -6.56 0.16466208476517755 -0.46964490263459335 0.2963917525773196 42.32
                      5.680183276059564 15.679123711340203 -19.519702176403204)
                epsilon100)
  (check-within (CSCL (flpoly> 1. -10. 35. -50.) 2.3 4.6 -6. 8.)
                (list 'calcSC:div-by-d
                      (flpoly> 1.0 -4.0)
                      -18.0 0.0 3.0 0.7666666666666666 0.0 -27.6 36.8
                      -2.3 37.03 23.0)
                epsilon100)
  (check-within (CSCL (flpoly> 1. -10. 35. -50. 24.) 2.3 4.6 -6. 8.00000000000001)
                (list 'calcSC:almost-factor
                      (flpoly> 1.0 -4.0 2.999999999999986)
                      5.3290705182007514e-14 -1.7408297026122455e-13 -4.263256414560601e-14)
                (bigmargin 1))

  ;nextK
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:div-by-c 8. 9. 10. 6. 7.)
                (flpoly> 16.0 5.8 12.7 13.6 3.5)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:div-by-c 8. 9. 0. 6. 7.)
                (flpoly> -112. -53. -54. -55.)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:almost-factor 8. 9. 10. 6. 7.)
                (flpoly> 11. 12. 13.)
                epsilon100)

  ;newest
  (define (NL P K tFlag a b c d f g h u v a1 a3 a7)
    (define-values (u+ v+)(newest P K tFlag a b c d f g h u v a1 a3 a7))
    (list u+ v+))
  (check-within (NL (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:almost-factor 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (NL (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-d 1. 5. -0.8908220965637230 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (NL (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-d 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(11.239868703446534 12.148466102764804) epsilon100)
  (check-within (NL (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-c 1. 5. 100.52892561983471 0. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(0. 0.) epsilon100)
  (check-within (NL (flpoly> 18. 19. 20. 21. 22.) (flpoly> 13. 14. 15. 16.) 'calcSC:div-by-c 1. 5. 6. 7. 8. 9. 10. 11. 12. 2. 3. 4.)
                '(11.047985250849212 12.029700344736144) epsilon100)
  (check-within (NL (flpoly> 765.85527498437887 -1347.293632350993 -2161.1901804835061 -7837.7065086597486 -3083.5325907341339 2512.6246767498906 5888.8148218838123 -224.71114833786896 4321.6465771244393 -4104.5415694069588 -358.02596267509489 -5940.1714091583599 -2813.1556404590783 -1218.7896752219331 -92.316085769292613 13.465814510071247 )
                        (flpoly> 765.85527498437887 569.21989433594013 -70.015121432447586 -702.31273591596982 -9385.9870113488287 7161.0962876975536 -6.3514328002929688 2149.7078857421875 2603.109375 -6064. -80480. 4108288. 128712704. -11601444864. -569620037632.)
                        'calcSC:div-by-c 4.2070203373260126e+029 -5.2749842363542267e+027 -5.5170988810118383e+027 -9.7406057385308503e+025 0.017655303899038365 -539.9094138852181 -1.9916002499454986e+031 7.080387980931846 3775.5567802833493
                         -1.2702606492846791e+028 -4.8274289306750895e+031 1.2166940450248765e+029)
                '(3.7978598044219325e-10 -5.868394095550277e-11) epsilon100)

  ;RealIT
  (define (RITL IS P K sss)
    (define-values (flag qP s)(RealIT IS P K sss))
    (list flag qP s))
  (check-within (RITL standard-iteration-scheme (flpoly> 1. 2. 3. 4. -5.) (flpoly> 1. 2. 3. 4.) 0.2)
                (list 'RealIT:normal
                      (flpoly> 1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                      0.6841243194530697)
                epsilon100)
  (check-within (RITL standard-iteration-scheme (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) 1.0)
                (list 'RealIT:maxiter flpoly-zero 0.0)
                epsilon100)
  (check-within (RITL standard-iteration-scheme (flpoly> 4.9679877220982345 9.29937913880471 -9.609506455896735 -2.5160214731778163 -6.029809381393797)
                        (flpoly> 8.514417957281449 0.5198895391395837 -9.66980775616132 0.45524621258751097) 3.5502909446276085)
                (list 'RealIT:zero-cluster
                      (flpoly> 4.9679877220982345 -6701.697712994184 7942.889509061441 -1976.5039946730667)
                      -1.4283341763844224)
                epsilon100)
  (check-within (RITL standard-iteration-scheme (flpoly> 1. 2. 3. 4. -5.) (flpoly> 1. 2. 3. 0.) 0.0)
                (list 'RealIT:normal
                      (flpoly> 1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                      0.6841243194530697)
                epsilon100)

  ;QuadIT
  (define (QITL IS P K u v)
    (define-values (flag qP sz lz)(QuadIT IS P K u v))
    (case flag
      [(QuadIT:normal)(list flag qP (real-part sz)(imag-part sz) (real-part lz)(imag-part lz))]
      [else flag]))
  (check-within (QITL standard-iteration-scheme (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) 6. 7.)
                'QuadIT:nonquad epsilon100)
  (check-within (QITL standard-iteration-scheme (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) -0.575630959115296 0.0828377502729989)
                (list 'QuadIT:normal (flpoly> 1.0 2.575630959115296 2.3944555573388273)
                      0.287815479557648 1.4160930801719076 0.287815479557648 -1.4160930801719076) (bigmargin 6))
  (check-within (QITL standard-iteration-scheme
                        (flpoly> -74.43388870038298 -48.684338183687615 82.95039531162064 2.082613677062014 60.82122424869209 -46.15017147716964 61.0180453610964 47.02754709444238 -5.330451975747479 91.51704177156668)
                        (flpoly> 38.515673952936254 7.252656554000609 -84.42246656861926 31.693388752691646 -27.265410421231138 -35.244767584584565 -97.79006609235279 8.92096535665003 -60.693225828975194)
                        14.737906787890154 56.6995805579966)
                (list 'QuadIT:normal (flpoly> -74.43388870038298    28.5525675415266  134.72025177002524 -168.93474867929848   88.79349933216068  46.45222659669343 -84.28416458872897   83.6875414818494)
                      -0.5188289035664532 0.907949839624714 -0.5188289035664532 -0.907949839624714)
                (bigmargin 1))
  #;(check-within (QITL standard-iteration-scheme
                        (flpoly> 765.8552749843789 -1347.293632350993 -2161.190180483506 -7837.706508659749 -3083.532590734134 2512.6246767498906 5888.814821883812 -224.71114833786896 4321.646577124439 -4104.541569406959 -358.0259626750949 -5940.17140915836 -2813.1556404590783 -1218.789675221933 -92.31608576929261 13.465814510071247)
                        (flpoly> 569.9471955954955 426.1973931512889 -39.26465304820874 -525.558286377151 -6935.288424258491 5283.823600793081 -1.6306656043934709 1584.535288608834 1907.3886808609604 -3739.1601002469033 -430.3641207148028 3278.5379900289245 -1171.8752324055004 1657.6923655682594 -2854.6807003064246)
                        7.080387980931846 3775.5567802833493)
                'QuadIT:nonconverging
                epsilon100);maxiter - because rounding errors
  ;FixedShift
  (define (FSL IS P K sr bnd)
    (define-values (fFlag pQ zs)(FixedShift IS P K sr bnd))
    (case fFlag
      [(FixedShift:maxiter)fFlag]
      [else (list pQ zs)]))
  (define (FSLIS [n 5])(struct-copy iteration-scheme standard-iteration-scheme [FixedShift n]))
  (check-within (FSL (FSLIS) (flpoly> 1. 2. 3. 4. 5.) (flpoly> 1. 2. 3. 4.) 1.0 2.0)
                (list (flpoly> 1.0 2.575630959115296 2.394455557338827)
                      '(0.28781547955764797+1.4160930801719078i 0.28781547955764797-1.4160930801719078i))
                epsilon100)
  (check-within (FSL (FSLIS) (flpoly> 1. 2. 3. 4. -5.) (flpoly> 1. 2. 3. 4.) 1.0 2.0)
                (list (flpoly> 1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                      '(0.6841243194530697))
                epsilon100)
  (check-within (FSL (FSLIS) (flpoly> 5.973052788152122 3.1198874346298604 4.732251119406017 3.6024342708537196 4.181120877543731)
                     (flpoly> 5.973052788152122 -7.411175697861289 -0.024070219044631358 -0.4006197810018648)
                     3.4548598408258635 0.586936423108628)
                (list (flpoly> 5.973052788152122 -4.285169564149636 5.5226517874526735)
                      '(-0.6198720538237862+0.6106098345570848i -0.6198720538237862-0.6106098345570848i))
                epsilon100)
  (check-within (FSL (FSLIS) (flpoly> 8.41755012535733 4.671578854715546 0.5931615068990723 0.7322427309831809 5.728464948833154)
                     (flpoly> 8.401638613441222 9.708937329579836 0.33872763171218045 0.1468471881337965)
                     0.24442525134432416 9.30559289538379)
                (list (flpoly> 8.41755012535733 13.252560535681688 8.27797623788355)
                      '(0.5097077863021263+0.6574273375997998i 0.5097077863021263-0.6574273375997998i))
                epsilon100)
  (check-equal? (FSL (FSLIS) (flpoly> 6.7460988725508955 5.98370659970934 6.157731644531755 4.907674864119937 3.8729258686230943)
                     (flpoly> 8.877633271400752 0.038665127484674225 5.24238410415498 4.852226488120647)
                     1.2246379011135278 9.917716291473479)
                'FixedShift:maxiter)
  (check-within (FSL (FSLIS 11) (flpoly> 61.52697196174651 36.82318279967228 -47.989940452833565)
                     (flpoly> -14.281125965172919 -30.810404431206194)
                     62.62559015912069 72.73878188097541)
                (list (flpoly> 61.52697196174651 75.78460263823895)
                      '(0.6332413020876496))
                epsilon100)
  #;(check-within (FSL (FSLIS 18) (flpoly> -74.46775787726362 90.3506061511408 -41.6749987910501 -12.605712335088313 -3.9257546925351363 -66.56163578033919 -36.151837492264384)
                     (flpoly> 55.20898627198051 41.74299097679142 23.90535938840239 19.045011969600466 -21.305286565679026 1.629283218386334)
                     26.907593802730446 1.2786560845469381)
                (list (flpoly> -74.46775787726362 172.36524977999846 -206.62332203773178 157.35777413703312 -108.18276080133784)
                      '(-0.5506721698539164+0.17588035331998092i -0.5506721698539164-0.17588035331998092i))
                epsilon100);maxiter - because ...
;|#
  ;Roots
  (define (RL P [IS (make-iteration-scheme)])
    (define-values (flag rts)(roots P #:iteration-scheme IS))
    (list flag (sort (for/list ([r (in-list rts)])
                       (if (= 0 (imag-part r)) (real-part r) r))
                     (λ (x y) (if (= (real-part x)(real-part y))
                                  (> (imag-part x)(imag-part y))
                                  (< (real-part x)(real-part y)))))))
  (check-within (RL (flpoly> 1. 2. 1. 0. 0.))
                '(roots:normal (-1. -1. 0. 0.))
                epsilon.0)
  (check-within (RL (flpoly> 1. 1. 1. 1. 1.))
                '(roots:normal (-0.8090169943749475+0.5877852522924729i
                                -0.8090169943749475-0.5877852522924729i
                                0.3090169943749474+0.9510565162951535i
                                0.3090169943749474-0.9510565162951535i))
                epsilon10)
  (check-within (RL (flpoly> 1. 2. 3. 4. 5.))
                '(roots:normal (-1.287815479557648+0.8578967583284905i
                                -1.287815479557648-0.8578967583284905i
                                0.287815479557648+1.4160930801719078i
                                0.287815479557648-1.4160930801719078i))
                epsilon10)
  (check-within (RL (flpoly> 1. 2. 3. 4. -5.))
                '(roots:normal (-2.0591424445683537
                                -0.3124909374423581+1.8578744391719895i
                                -0.3124909374423581-1.8578744391719895i
                                0.6841243194530697))
                epsilon10)
  (check-within (RL (flpoly> 1. 3. 1. 0.08866210790363471))
                '(roots:normal (-2.632993161855452
                                -0.18350341911302884
                                -0.1835034190315191))
                epsilon10)
  ;irritatingly difficult (flpoly-from-roots .9998 .9999 1. 1.003 1.003)
  (check-within (RL (flpoly> 1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
                '(roots:normal (0.9998
                                0.9999
                                1.0
                                1.003
                                1.003))
                (bigmargin 11))
  (check-within (RL (flpoly> 1e-8 1e-16 1e-20 -1e25 38.5))
                '(roots:normal (-50000000000.0+86602540378.44386i
                                -50000000000.0-86602540378.44386i
                                3.85e-24
                                100000000000.0))
                epsilon.0)
  (check-within (RL (flpoly> 1. -1.1262458658846637 -1.0101179104905715 0.1369529023140107  -0.07030543743385387  0.34354611896594955  0.7685557744974647  0.9049868924344322 -0.4694264319569345))
                '(roots:normal (-1.00470119265642
                                -0.6385228013511156+0.6232370795625065i
                                -0.6385228013511156-0.6232370795625065i
                                0.16462177207475362+0.9168019517176714i
                                0.16462177207475362-0.9168019517176714i
                                0.37998534697611247
                                1.1475571613888245
                                1.5512066087288707))
                epsilon10)
  (check-within (RL (flpoly> 91.18809308091258 10.754641992264794 -69.33386824593055 75.32381621826295 -99.6568435171208 -8.055652043683352)
                    (iteration-scheme 16 7 6 0 13 6 6))
                '(roots:normal (-1.4211122825020175
                                -0.0761433179981868
                                0.18998072135406274+0.8836475713376982i
                                0.18998072135406274-0.8836475713376982i
                                0.9993550538048728))
                epsilon10)
  (check-within (RL (flpoly> 89.66884488498786 -5.035976424692905 -27.674824222075614 -96.72180780166202 -76.0750414392931 74.2881927760188 -18.803978038771874 -88.40539985995814)
                    (iteration-scheme 10 12 9 0 8 20 5))
                '(roots:normal (-0.8415758009696521+0.238152739346124i
                                -0.8415758009696521-0.238152739346124i
                                -0.3656188900542874+1.1496345853579042i
                                -0.3656188900542874-1.1496345853579042i
                                0.5869751784061364+0.5817789453984389i
                                0.5869751784061364-0.5817789453984389i
                                1.296600966778984))
                epsilon10)
  (check-within (RL (flpoly> -40.64181224757269 -32.38161144204791 40.40535730410238 -65.15400236286979 -62.242148105606155 50.1741360957316 35.03883110547369 72.04602337106431 -60.304657589497225)
                    (iteration-scheme 6 15 17 0 13 13 11))
                '(roots:normal (-1.4278711153456562+0.20522664007256347i
                                -1.4278711153456562-0.20522664007256347i
                                -0.3924569734187341+0.799423579895323i
                                -0.3924569734187341-0.799423579895323i
                                0.6951414539634508+1.0992008490881526i
                                0.6951414539634508-1.0992008490881526i
                                0.7268085894914331+0.057272261653429815i
                                0.7268085894914331-0.057272261653429815i))
                epsilon10)
  (check-within (RL (flpoly> 49.710497758300875 83.86411816900053 -36.84017911151918 -14.016998958665823 17.093717575886586 -58.21731735700788 -55.75463399220348 -1.192533142875618)
                    (iteration-scheme 10 7 13 0 11 10 7))
                '(roots:normal (-1.9038858291033882
                                -0.740897582574855+0.3020074801637734i
                                -0.740897582574855-0.3020074801637734i
                                -0.02189268218917173
                                0.34616045877917445+0.8686851231541562i
                                0.34616045877917445-0.8686851231541562i
                                1.028202297696444))
                epsilon10)
  (check-within (RL (flpoly> 22.709304169643517 -87.36732242917714 13.288056236672148 -41.39643819314873 75.18712911729767 -35.487285112346356 -93.38667030083654 -18.78550828140827 39.560341795103426 72.3237416807884 56.78347959438429 58.343051452039475 -31.924565751177653 67.97234288841659 13.739862585880672 57.482326672487886 2.103801825454184 -96.50241534051075 17.05682765408889)
                    (iteration-scheme 18 5 6 0 17 8 16))
                '(roots:maxiter ())
                epsilon100)
  (check-within (RL (flpoly> -17.756065857424794 25.893174382341186 -60.51441252673925 0.0 67.74493116488347)
                    (iteration-scheme 8 19 8 0 9 17 6))
                '(roots:normal (-0.8443057836142638
                                0.5902962670087036+1.9181033950461768i
                                0.5902962670087036-1.9181033950461768i
                                1.1219852897128721))
                epsilon100)
  (check-within (RL (flpoly> -188.89404654362278 0.0 0.0)
                    (iteration-scheme 8 19 8 0 9 17 6))
                '(roots:normal (0.0 0.0))
                epsilon100)
  (check-within (RL (flpoly> -188.89404654362278)
                    (iteration-scheme 8 19 8 0 9 17 6))
                '(roots:degree<1 ())
                epsilon100)
  (check-within (RL (flpoly>  159229057.05739117 -78888201.05066945 -399652902.8637534 387714558.0458791 87147247.41927719 -373541203.5956339 3936235.3638518006)
                    (iteration-scheme 13 18 9 0 14 10 5))
                '(roots:normal (-1.5655085971707023
                                -0.8960862217975081
                                0.01056487103935344
                                0.7583497020117624+0.769096584596765i
                                0.7583497020117624-0.769096584596765i
                                1.4297690179411084))
                epsilon100)
  (check-within (RL (flpoly> 214542993.69446766 15771022.467699721 890012027.745492 -165071836.07194433)
                    (iteration-scheme 15 10 20 0 13 15 13))
                '(roots:normal
                  (-0.12844930880665237+2.0442655956929086i
                   -0.12844930880665237-2.0442655956929086i
                   0.1833887714229446))
                epsilon100)
  (check-within (RL (flpoly> -8016962.537211122 -595601492.2906611 715047653.6769369 -22040839.97303778 654164003.3990982 42327521.39674103 80334718.612445 392646145.08107615 -31915455.976172626 529782579.1482458 401148371.69478726)
                    (iteration-scheme 7 20 9 0 20 19 11))
                '(roots:normal (-75.47507382991347
                                -0.6739936254864842+0.08281641620251147i
                                -0.6739936254864842-0.08281641620251147i
                                -0.47209709029395136+0.8952802963210883i
                                -0.47209709029395136-0.8952802963210883i
                                0.13029508476198612+0.936649222491123i
                                0.13029508476198612-0.936649222491123i
                                0.7769826257300415+0.5845313511419681i
                                0.7769826257300415-0.5845313511419681i
                                1.660037310741913))
                epsilon100)
  (check-within (RL (flpoly> 2.2257803969463154e-89 4.804973432196881e+55 -9254052903233.797 -7.173079397063823e+57 -3.643231025848551e-43 1.8776093704027008e-13 9.68826810716646e+82 5.953885255942153e-52 12473534698247728.0)
                    (iteration-scheme 14 11 18 0 19 20 15))
                '(roots:maxiter ())
                epsilon10)
  (check-within (RL (flpoly> -9.178897924537484e-49 -583000230.8972292 4.279804679145892e+62 -1.3555834609925188e-90 1.3976480650507842e+86 9.191199813915781e+48 2.72563841355331e+56 3.338044256510494e-45 9.616856917344557e+17)
                    (iteration-scheme 12 8 15 0 6 17 17))
                '(roots:maxiter ())
                epsilon100)
  (check-within (RL (flpoly> 1.3931473576870403e-38 -765.019962127356 -6.973551088128851e-73 8.856399693091199e-78 4.3775265455538223e-94 4.081553106420452e-27 -3.3408648019889094e-90 -4.7731718869925835e-70 -7.376023459763471e-17 5.002146579894817e+32 9.081327081405566e-42 3.556442467900932e+48 9.916740926607073e-79 -5.975430203343156e+43 -8.070681774686512e+98)
                    (iteration-scheme 11 8 14 0 14 17 13))
                '(roots:maxiter ())
                epsilon10)
  (check-within (RL (flpoly> 5.899323652745066e+98 -3.268616690736327e+28 -1.8171398662880743e-21 -9.182021624841844e-48 -0.0009582829713641801)
                    (iteration-scheme 11 14 16 0 17 7 19))
                '(roots:maxiter ())
                epsilon.0)


  ;next-ones have quite a big error comparing P with (flpoly-from-roots (roots P))
  ;TODO: investigate
  (check-within (RL (flpoly> 152477314.02538288 -191980602.43688652 609952937.2769084 -318365436.12520283 -187837307.74616426 -23048368.602685448 -370828396.5539714 -529130218.3615113 -123387300.88296044 423635917.5689908 593.3435119165806 249353152.52116847 -49473153.69341767 343062074.73545027 -18859194.72846794 -925302.59490747))
                '(roots:normal (-0.9940833828509659
                                -0.7577204961201565+0.5571103975024048i
                                -0.7577204961201565-0.5571103975024048i
                                -0.3686395087131277+0.7367779543475123i
                                -0.3686395087131277-0.7367779543475123i
                                -0.03122981669343392
                                0.08669039865108745
                                0.32225545895602825+1.89418075458199i
                                0.32225545895602825-1.89418075458199i
                                0.3645204204151995+1.1008398063471747i
                                0.3645204204151995-1.1008398063471747i
                                0.42412140113937313+0.6613616135339837i
                                0.42412140113937313-0.6613616135339837i
                                0.9876003122893545
                                1.2410244343925487))
                epsilon10)
  (check-within (RL (flpoly> 323567969.8134451 -315295709.22543466 -703506171.2655511 -211962752.43570948 554725026.0003369 1249793.8748204112 28459313.912715524 -651790467.7979249 -31542556.93502626 464511198.4179255 77106973.0883564 -50099893.33604723 -94387402.11422235 -106.69235908228438 388627722.11239517 -690475900.500899))
                '(roots:normal (-1.0257392004024477+0.6626987848351278i
                                -1.0257392004024477-0.6626987848351278i
                                -0.9759828789236693+0.27962552916677724i
                                -0.9759828789236693-0.27962552916677724i
                                -0.48904037099529135+0.8528650728813355i
                                -0.48904037099529135-0.8528650728813355i
                                -0.14058960488416075+0.9979401511411738i
                                -0.14058960488416075-0.9979401511411738i
                                0.3955087197236365+0.7714289963168508i
                                0.3955087197236365-0.7714289963168508i
                                0.7833020876493673+0.641810138744502i
                                0.7833020876493673-0.641810138744502i
                                0.9278611007273394+0.21395118987895495i
                                0.9278611007273394-0.21395118987895495i
                                2.023794535668963))
                epsilon10)

  (define (inv-check F0 ans)
    (define rts:type (car ans))
    (define rts (cadr ans))
    (case rts:type
      [(roots:normal)
       (define mx (cadr (abs-coefficient-interval F0)))
       (define F1 (apply flpoly-from-roots #:s (flpoly-reverse-coefficient F0 0) rts))
       (sqrt (for/sum ([i (in-range (+ (flpoly-degree F1) 1))]) (expt (/ (- (flpoly-coefficient F0 i) (flpoly-coefficient F1 i)) mx) 2)))]
      [else
       0.0]))

  (let ();for searching branches
    (define (rdm)
      (* (if (< (random) 0.5) -1.0 1.0)
         (random)
         (expt 10 (- (random 200) 100))))
    (for ([i (in-range 1000000000)])
      (define p (for/list ([i (in-range (+ (random 17) 3))])(rdm)))
      (define P (flpolyL> p))
      (define r (for/list ([i (in-range 7)]) (+ 5 (random 16))))
      (define out (open-output-string))
      (define ans
        (parameterize ([current-output-port out])
          (with-handlers ([exn:fail? (λ (e) (printf "This Failed: ~a\n" e) '(error ()))])
            (RL P (apply iteration-scheme r)))))
      (define err (inv-check P ans))
      (define S (get-output-string out))
      (unless (equal? "" S)
        (displayln i)
        (displayln S)
        (displayln `(check-within (RL (flpoly> ,@p) (iteration-scheme ,@r))
                                  ',ans
                                  epsilon.0))
        (displayln "------------------------------------------------"))
      (unless (and (< err (bigmargin 8)))
        (define err+ (inv-check P (RL P)))
        (unless (< err+ (bigmargin 4))
          (displayln i)
          (displayln err)
          (displayln `(check-within (RL (flpoly> ,@p))
                                    ',ans
                                    epsilon.0))
          (displayln "------------------------------------------------")))))
  )
