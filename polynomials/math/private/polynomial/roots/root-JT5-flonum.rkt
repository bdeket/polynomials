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


(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))
(define +FLT_MIN (floating-point-bytes->real (bytes #b00000000 #b00000000 #b00000000 #b00000001)))
(define +FLT_MAX (floating-point-bytes->real (bytes #b11111111 #b11111111 #b11111111 #b01111110)))

(struct iteration-scheme ([ZeroShift : Nonnegative-Integer][1Root : Nonnegative-Integer][Multiplier : Nonnegative-Integer][FixedShift : Nonnegative-Integer][QuadShift : Nonnegative-Integer][QuadFixedShift : Nonnegative-Integer][LinShift : Nonnegative-Integer]))
(define standard-iteration-scheme (iteration-scheme 5 20 20 0 20 5 10))

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
    [(= a0 0) (values 0.0 0.0 (fl* -1.0 (fl/ a1 a2)) 0.0)]
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
        (values R I R (- I))]
       [else
        ;real zeros
        (define D** (cond [(> a1/2 0) (- D*)][else D*]))
        (define Z1 (/ (- D** a1/2) a2))
        (cond
          [(= Z1 0) (values 0.0 0.0 0.0 0.0)]
          [else     (values (/ (/ a0 Z1) a2) 0.0 Z1 0.0)])])]))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision [P : flpoly][u : Flonum][v : Flonum])
  (begin
    (define-values (qP rP)(flpoly/p-QR P (flpoly> 1.0 u v)))
    (values qP
            (flpoly-coefficient rP 0)
            (fl- (flpoly-coefficient rP 0)(fl* u (flpoly-coefficient rP 1)))
            (flpoly-coefficient rP 1)))
  #;(begin
    (define b (flpoly-reverse-coefficient P 0))
    (define a (fl- (flpoly-reverse-coefficient P 1)(fl* u b)))
    (define R
      (for/fold ([ans : (Listof Flonum) (list a b)])
                ([i : Integer (in-range (- (flpoly-degree P) 2) -1 -1)])
        (cons (fl- (flpoly-coefficient P i)
                   (fl+ (fl* (car ans) u) (fl* (cadr ans) v)))
              ans)))
    (list (flpoly< (cddr R))
          (+ (car R)(* u (cadr R)))
          (car R)
          (cadr R))))

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
     (define h (fl* v b))
     (cond
       [(fl>= (flabs d) (flabs c))
        ;TYPE = 2 indicates that all formulas are divided by d
        (define e (fl/ a d))
        (define f (fl/ c d))
        (define g (fl* u b))
        (define a1 (fl- (fl* f b) a))
        (define a3 (fl+ (fl* e (+ g a)) (fl* h (/ b d))))
        (define a7 (fl+ h (fl* c+ud e)));(f+u)a=(c+ud)a/d=(c+ud)*e
        (values 'calcSC:div-by-d qK c+ud c d e f g h a1 a3 a7)]
       [else
        ;TYPE = 1 indicates that all formulas are divided by c
        (define e (fl/ a c))
        (define f (fl/ d c))
        (define g (fl* e u))
        (define a1 (fl- b (fl* a f)))
        (define a3 (fl+ (fl* e a) (fl* (fl+ g (fl/ h c)) b)))
        (define a7 (fl+ (fl* h f) (fl* c+ud e)));gd+a=eud+a=a(ud/c+1)=a/c(c+ud)=(c+ud)*e
        (values 'calcSC:div-by-c qK c+ud c d e f g h a1 a3 a7)])]))

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
  : (Values Flonum Flonum)
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     (values 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (cond
         [(equal? tFlag 'calcSC:div-by-c)
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
        (values 0.0 0.0)]
       ;!!!if temp ≈ 0.0 these values blow up. Is this a good idea?
       [else
        (values (fl+ (fl* -1.0 (fl/ (fl+ (fl* u (fl+ c3 c2)) (fl* v (fl+ (fl* b1 a1)(fl* b2 a7)))) temp)) u)
                (fl* v (fl+ 1.0 (fl/ c4 temp))))])]))

(define (calcSC->nextK [qP : flpoly][K : flpoly]
                       [a : Flonum][b : Flonum][u : Flonum][v : Flonum])
  : flpoly
  (define-values (tFlag qK c+ud c d e f g h a1 a3 a7)(calcSC K a b u v))
  (define sK (flpoly+ (flpoly-shift qK 1) (const-flpoly d)))
  (case tFlag
    [(calcSC:almost-factor)
     (nextK qP sK
            tFlag a b 0.0 0.0 0.0)]
    [else
     (nextK qP sK tFlag a b a1 a3 a7)]))
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
       (values 'RealIT:normal qP s)]
      [(> j (iteration-scheme-LinShift IS))
       (values 'RealIT:maxiter flpoly-zero 0.0)]
      [(and (>= j 2)
            (fl<= (abs t) (fl* 0.001 (flabs (- s t)))) (> mp omp))
       ;A cluster of zeros near the real axis has been encountered;
       ;Return with iFlag set to initiate a quadratic iteration
       (values 'RealIT:zero-cluster K s)]
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
       (define sP (flpoly+ (flpoly-shift qP 1) (const-flpoly b)))
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
       (cond
         [(fl<= mp (fl* 20.0 ee))
          ;Iteration has converged sufficiently if the polynomial
          ;value is less than 20 times this bound
          (values 'QuadIT:normal sP (+ szr (* +i szi)) (+ lzr (* +i lzi)))]
         ;Stop iteration after 20 steps
         [(> j (iteration-scheme-QuadShift IS))
          (values 'QuadIT:maxiter flpoly-zero 0 0)]
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
               (define-values (qP+ a+ub+ a+ b+)(QuadraticSyntheticDivision P u+ v+))
               (define sP+ (flpoly+ (flpoly-shift qP+ 1) (const-flpoly b+)))
               (define K+
                 (for/fold ([K+ : flpoly K])
                           ([i : Integer (in-range (iteration-scheme-QuadFixedShift IS))])
                   (calcSC->nextK sP+ K+ a+ b+ u+ v+)))
               (values 0 #t u+ v+ a+ b+ sP+ K+)]
              [else
               (values j tried? u v a b sP K)]))
          ;Calculate next K polynomial and new u and v
          (define-values (tFlag Ki ui vi)(calcSC->K+newest P sP+ K+ a+ b+ u+ v+))
          (cond
            [(fl= vi 0.0)
             ;If vi is zero, the iteration is not converging
             (values 'QuadIT:nonconverging flpoly-zero 0 0)]
            [else
             (loop (+ j+ 1) mp (flabs (fl/ (fl- vi v+) vi)) tried?+
                   ui vi Ki)])])])))

;The fixed shift
(define (FixedShift [IS : iteration-scheme]
                    [P : flpoly][K : flpoly]
                    [sr : Flonum][bnd : Flonum])
  : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
  (define u (* -2 sr))
  (define v bnd)
  ;Evaluate polynomial by synthetic division
  (define-values (qP a+ub a b)(QuadraticSyntheticDivision P u v))
  (define sP (flpoly+ (flpoly-shift qP 1) (const-flpoly b)))
  ;fixed shifts: do a fixed shift, if quadratic or linear convergence is detected try to start stage 3.
  ;If unsuccessful continue the fixed shifts
  (let loop ([j : Integer 0][K_old : flpoly K]
             [vv_old : Flonum v][ss_old : Flonum sr][tv_old : Flonum 0.0][ts_old : Flonum 0.0]
             [quadConvergingLimit : Flonum 0.25][linConvergingLimit : Flonum 0.25])
    (cond
      [(<= (iteration-scheme-FixedShift IS) j) (values 'FixedShift:maxiter flpoly-zero '())]
      [else
       ;Calculate next K polynomial and estimate vv
       (define-values (tFlag K uu vv)(calcSC->K+newest P sP K_old a b u v))
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
          (define tvv (if (fl< tv tv_old) (fl* tv tv_old) 1.))
          (define tss (if (fl< ts ts_old) (fl* ts ts_old) 1.))
          ;Compare with convergence criteria
          (define quadConverging? (fl< tvv quadConvergingLimit))
          (define linConverging? (fl< tss linConvergingLimit))
          (cond
            [(or linConverging? quadConverging?)
             ;At least one sequence has passed the convergence test.
             (define (tryQuad [K : flpoly][ui : Flonum][vi : Flonum][triedLin? : Boolean][quadConvergingLimit : Flonum][linConvergingLimit : Flonum])
               : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
               (define-values (qFlag qp sz lz)(QuadIT IS P K ui vi))
               ;decrease the convergence criterion for if Quadratic iteration fails, 
               (define  qCL (fl* quadConvergingLimit 0.25))
               (cond
                 [(equal? qFlag 'QuadIT:normal)
                  (values 'FixedShift:normal (flpoly-shift qp -1) (list sz lz))]
                 [(and (not triedLin?) linConverging?)
                  (tryLin ss #t qCL linConvergingLimit)]
                 [else
                  (loop (+ j 1) K vv ss tv ts qCL linConvergingLimit)]))
             (define (tryLin [sss : Flonum][triedQuad? : Boolean][quadConvergingLimit : Flonum][linConvergingLimit : Flonum])
               : (Values (U 'FixedShift:normal 'FixedShift:maxiter) flpoly (Listof Number))
               (define-values (iFlag F z)(RealIT IS P K sss))
               ;decrease the convergence criterion for if Linear iteration fails, 
               (define lCL (fl* linConvergingLimit 0.25))
               (cond
                 [(equal? iFlag 'RealIT:normal)
                  (values 'FixedShift:normal F (list z))]
                 [(equal? iFlag 'RealIT:zero-cluster)
                  ;If linear iteration signals an almost double real zero, attempt quadratic iteration
                  (tryQuad F (fl* -2.0 z) (fl* z z) #t quadConvergingLimit lCL)]
                 [(and (not triedQuad?) quadConverging?)
                  (tryQuad K uu vv #t quadConvergingLimit lCL)]
                 [else
                  (loop (+ j 1) K vv ss tv ts quadConvergingLimit lCL)]))
             ;Choose iteration according to the fastest converging sequence, if it fails try the other one (if it is converging)
             (cond
               [(and linConverging? (or (not quadConverging?) (< tss tvv)))
                (tryLin ss #f quadConvergingLimit linConvergingLimit)]
               [else
                (tryQuad K uu vv #f quadConvergingLimit linConvergingLimit)])]
            [else
             (loop (+ j 1) K vv ss tv ts quadConvergingLimit linConvergingLimit)])])])))

;ZeroShift
(define (ZeroShift [maxiter : Integer][P : flpoly][K : flpoly])
  (define aa (flpoly-coefficient P 0))
  (define bb (flpoly-coefficient P 1))
  (for/fold  ([K : flpoly K])
             ([iter : Integer (in-range maxiter)])
    (define zerok (<= (abs (flpoly-coefficient K 0)) (* (abs bb) epsilon10)))
    ;in original zerok depends on scaling form: <= is for scaled, otherwise only if K[0]=0
    (cond
      [zerok ;Use unscaled form of recurrence
       (flpoly-shift K -1)]
      [else ;Use scaled form of recurrence if value of K at 0 is nonzero
       (define t (- (/ aa (flpoly-coefficient K 0))))
       (flpoly-shift (flpoly+ P (flpoly*s K t)) -1)])))

(define (1root [IS : iteration-scheme][P : flpoly][angle : Number])
  : (Values (U '1root:maxiter '1root:normal) flpoly Number (Listof Number))
  (define N (flpoly-degree P))
  ;Find the largest and smallest moduli of the coefficients
  (define P+ (flpoly*s P (flpoly-bestscale P)))
  ;Compute lower bound on moduli of zeros
  (define bnd (roots-mod-lower-bound P))
  ;Compute the (scaled) derivative as the initial K polynomial => K = p'/N
  #;(define K_0 (for/vector ([i (in-range N)]
                           [ai (in-vector P+)])
                (if (= i 0) ai (/ (* (- N i) ai) N))))
  (define K_0 (flpoly*s (flpoly-diff P) (/ 1. N)))
  ;do 5 steps with no shift
  (define K_1 (ZeroShift (iteration-scheme-ZeroShift IS) P+ K_0))
  ;Loop to select the quadratic corresponding to each new shift
(println (list (pp P+) (pp K_0) (pp  K_1) bnd))
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

(define (roots [P : flpoly] #:iteration-scheme [IS : iteration-scheme standard-iteration-scheme])
  : (Values (U 'roots:degree<1 'roots:maxiter 'roots:normal) (Listof Number))
  (cond
    [(< (flpoly-degree P) 1) (values 'roots:degree<1 '())]
    ;Do a quick check to see if leading coefficient is 0
    ;The leading coefficient is zero. No further action is taken. Program terminated
    ;[(= 0.0 (rf P 0)) (label roots-leadingzero) 'leading-zero]
    ;can not happen with flpoly
    [else
     ;Remove zeros at the origin, if any
     (define s@0 (for/sum : Integer ([i : Integer (in-range (flpoly-degree P))]
                                     #:break (not (= 0 (flpoly-coefficient P 0))))
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
           "../poly-flonum.rkt")
  (define (bigmargin n) (* (expt 10 n) epsilon100))
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
                (flpoly> 16.0 5.8 12.7 13.6)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:div-by-c 8. 9. 0. 6. 7.)
                (flpoly> 0. -112. -53. -54.)
                epsilon100)
  (check-within (nextK (flpoly> 16. 17. 18. 19.) (flpoly> 11. 12. 13.) 'calcSC:almost-factor 8. 9. 10. 6. 7.)
                (flpoly> 0. 0. 11. 12.)
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
                (list 'QuadIT:normal (flpoly> 1.0 2.575630959115296 2.3944555573388273 0.)
                      0.287815479557648 1.4160930801719076 0.287815479557648 -1.4160930801719076) (bigmargin 6))
  (check-within (QITL standard-iteration-scheme
                        (flpoly> -74.43388870038298 -48.684338183687615 82.95039531162064 2.082613677062014 60.82122424869209 -46.15017147716964 61.0180453610964 47.02754709444238 -5.330451975747479 91.51704177156668)
                        (flpoly> 38.515673952936254 7.252656554000609 -84.42246656861926 31.693388752691646 -27.265410421231138 -35.244767584584565 -97.79006609235279 8.92096535665003 -60.693225828975194)
                        14.737906787890154 56.6995805579966)
                (list 'QuadIT:normal (flpoly> -74.43388870038298    28.5525675415266  134.72025177002524 -168.93474867929848   88.79349933216068  46.45222659669343 -84.28416458872897   83.6875414818494   -4.263256414560601e-14)
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
  )
