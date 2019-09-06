#lang racket/base

(require math/flonum)

(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))

(define RADFAC (/ (angle -1) 180));Degrees - to - radians conversion factor = pi/180
(define cosr (cos (* 94 RADFAC)));-.069756474
(define sinr (sin (* 94 RADFAC))); .99756405

(define s!
  (case-lambda [(a b)(set-box! a b)]
               [(a b c)(vector-set! a b c)]))
(define rf
  (case-lambda [(a)(if (vector? a)a(unbox a))]
               [(a b)(vector-ref a b)]))

(define (isZero v)(= v 0))

; CALCULATE THE ZEROS OF THE QUADRATIC A*Z**2+B1*Z+C.
; THE QUADRATIC FORMULA, MODIFIED TO AVOID
; OVERFLOW, IS USED TO FIND THE LARGER ZERO IF THE
; ZEROS ARE REAL AND BOTH ZEROS ARE COMPLEX.
; THE SMALLER REAL ZERO IS FOUND DIRECTLY FROM THE
; PRODUCT OF THE ZEROS C/A.
(define (Quad A B1 C szr* szi* lzr* lzi*)
  (define B (box 'undefined))(define E (box 'undefined))(define D (box 'undefined))
  (define (goto00)
    (cond
      [(not (= A 0)) (goto20)]
      [else
       (s! szr* 0.0)
       (when (not (= B1 0)) (s! szr* (- (/ C B1))))
       (s! lzr* 0)
       (goto10)]))
  (define (goto10)
    (s! szi* 0)
    (s! lzi* 0))
  (define (goto20)
    (cond
      [(not (= C 0)) (goto30)]
      [else
       (s! szr* 0)
       (s! lzr* (- (/ B1 A)))
       (goto10)]))
  ;compute Discriminant avoiding overflow
  (define (goto30)
    (s! B (/ B1 2))
    (cond
      [(< (abs (rf B)) (abs C)) (goto40)]
      [(s! E (- 1 (* (/ A (rf B))(/ C (rf B)))))
       (s! D (* (sqrt (abs (rf E)))(abs (rf B))))
       (goto50)]))
  (define (goto40)
    (s! E A)
    (when (< C 0) (s! E (- A)))
    (s! E (- (* (rf B) (/ (rf B) (abs C))) (rf E)))
    (s! D (* (sqrt (abs (rf E))) (sqrt (abs C))))
    (goto50))
  (define (goto50)
    (cond
      [(< (rf E) 0) (goto60)]
      [else
       ;real zeros
       (when (> (rf B) 0) (s! D (- (rf D))))
       (s! lzr* (/ (+ (- (rf B)) (rf D)) A))
       (s! szr* 0)
       (when (not (= (rf lzr*) 0)) (s! szr* (/ (/ C (rf lzr*)) A)))
       (goto10)]))
  (define (goto60)
    ;comples conjugate zeros
    (s! szr* (- (/ (rf B) A)))
    (s! lzr* (rf szr*))
    (s! szi* (abs (/ (rf D) A)))
    (s! lzi* (- (rf szi*))))

  (goto00))
(module+ test
  (define szr* (box 'undefined))(define szi* (box 'undefined))
  (define lzr* (box 'undefined))(define lzi* (box 'undefined))
  (Quad 1 6 3 szr* szi* lzr* lzi*)
  (list (list (rf szr*)(rf szi*))
        (list (rf lzr*)(rf lzi*))))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision NN u v p q* a* b*)
(println (list 'QuadraticSyntheticDivision NN u v p q* a* b*))
  (define b (rf p 0))
  (s! q* 0 b)
  (define a (- (rf p 1) (* b u)))
  (s! q* 1 a)
  (for ([i (in-range 2 NN)])
    (s! q* i (- (rf p i) (+ (* a u)(* b v))))
    (set! b a)
    (set! a (rf q* i)))
  (s! a* a)
  (s! b* b)
(println (list '-> 'a (rf a*) 'b (rf b*) 'q (rf q*)))
  )

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
(define (calcSC N a b a1* a3* a7* c* d* e* f* g* h* K u v qk*)
  (define dumFlag 3) ;type=3 indicates the quadratic is almost a factor of K
  ;Synthetic division of K by the quadratic 1, u, v
  (QuadraticSyntheticDivision N u v K qk* c* d*)
  (define c (rf c*))(define d (rf d*))
  (cond
    [(and (<= (abs c) (* epsilon100 (abs (rf K (- N 1)))))
          (<= (abs d) (* epsilon100 (abs (rf K (- N 2))))))
     dumFlag]
    [else
     (define h (* v b))(s! h* h)
     (cond
       [(>= (abs d) (abs c))
        (set! dumFlag 2);TYPE = 2 indicates that all formulas are divided by d
        (define e (/ a d))(s! e* e)
        (define f (/ c d))(s! f* f)
        (define g (* u b))(s! g* g)
        (s! a3* (+ (* e (+ g a)) (* h (/ b d))))
        (s! a1* (- (* f b) a))
        (s! a7* (+ h (* (+ f u) a)))]
       [else
        (set! dumFlag 1);TYPE = 1 indicates that all formulas are divided by c
        (define e (/ a c))(s! e* e)
        (define f (/ d c))(s! f* f)
        (define g (* e u))(s! g* g)
        (s! a3* (+ (* e a) (* (+ g (/ h c)) b)))
        (s! a1* (- b (* a (/ d c))))
        (s! a7* (+ (* g d) (* h f) a))])
     dumFlag]))

;Computes the next K polynomials using the scalars computed in calcSC_ak1
(define (nextK N tFlag a b a1 a3* a7* K* qk qp)
  (cond
    [(= tFlag 3)
     ; use unscaled form of the recurrence
     (s! K* 0 0)(s! K* 1 0)
     (for ([i (in-range 2 N)])(s! K* i (rf qk (- i 2))))]
    [else
     (define temp (if (= tFlag 1) b a))
     (cond
       [(> (abs a1) (* epsilon10 (abs temp)))
        (define a7 (/ (rf a7*) a1))(s! a7* a7)
        (define a3 (/ (rf a3*) a1))(s! a3* a3)
        (s! K* 0 (rf qp 0))
        (s! K* 1 (- (rf qp 1) (* a7 (rf qp 0))))
        (for ([i (in-range 2 N)])
          (s! K* i (+ (rf qp i) (* -1 a7 (rf qp (- i 1))) (* a3 (rf qk (- i 2))))))]
       [else
        ;If a1 is nearly zero, then use a special form of the recurrence
        (define a7 (rf a7*))(define a3 (rf a3*))
        (s! K* 0 0)
        (s! K* 1 (* -1 a7 (rf qp 0)))
        (for ([i (in-range 2 N)])
          (s! K* (+ (* a3 (rf qk (- i 2))) (* -1 a7 (rf qp (- i 1))) )))])]))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest tFlag uu* vv* a a1 a3 a7 b c d f g h u v K N p)
;(println (list 'newest tFlag uu* vv* a a1 a3 a7 b c d f g h u v K N p))
  (s! uu* 0)(s! vv* 0)
  (unless (= tFlag 3)
    (define a4 0)(define a5 0)
    (cond
      [(not (= tFlag 2))
       (set! a4 (+ a (* u b) (* h f)))
       (set! a5 (+ c (* (+ u (* v f)) d)))]
      [else
       (set! a4 (+ (* (+ a g) f) h))
       (set! a5 (+ (* (+ f u) c) (* v d)))])
    (define b1 (- (/ (rf K (- N 1))(rf p N))))
    (define b2 (- (/ (+ (rf K (- N 2)) (* b1 (rf p (- N 1))))
                     (rf p N))))
    (define c1 (* v b2 a1))
    (define c2 (* b1 a7))
    (define c3 (* b1 b1 a3))
    (define c4 (+ (- (+ c2 c3)) c1))
    (define temp (+ (- c4) a5 (* b1 a4)))
    (unless (= temp 0.0)
      (s! uu* (+ (- (/ (+ (* u (+ c3 c2)) (* v (+ (* b1 a1)(* b2 a7)))) temp)) u))
      (s! vv* (* v (+ 1.0 (/ c4 temp)))))))

; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT iFlag* NZ* sss* N p NN qp* szr* szi* K* qk*)
  (s! iFlag* 0)(s! NZ* 0)
  (define t 0)(define omp 0)(define s (rf sss*))
  (for ([j (in-naturals 1)])
    (define pv (rf p 0)); Evaluate p at s
    (s! qp* 0 pv)
    (for ([i (in-range 1 NN)])
      (set! pv (+ (* pv s) (rf p i)))(s! qp* i pv))
    (define mp (abs pv))
    ;Compute a rigorous bound on the error in evaluating p
    (define ms (abs s))
    (define ee (* 0.5 (abs (rf qp* 0))))
    (for ([i (in-range 1 NN)])
      (set! ee (+ (* ee ms) (abs (rf qp* i)))))
    ;Iteration has converged sufficiently if the polynomial
    ;value is less than 20 times this bound
    #:break (and (<= mp (* 20 epsilon.0 (- (* 2 ee) mp)))
                 (s! NZ* 1)(s! szr* s)(s! szi* 0))
    #:break (>= j 10)
    #:break (and (>= j 2)
                 (<= (abs t) (* 0.001 (abs (- s t)))) (> mp omp)
                 ;A cluster of zeros near the real axis has been encountered;
                 ;Return with iFlag set to initiate a quadratic iteration
                 (s! iFlag* 1)(s! sss* s))
    ;Return if the polynomial value has increased significantly
    (set! omp mp)
    ;Compute t, the next polynomial and the new iterate
    (define kv (rf K* 0))(s! qk* 0 kv)
    (for ([i (in-range 1 N)])
      (set! kv (+ (* kv s) (rf K* i)))(s! qk* i kv))
    (cond
      [(> (abs kv) (* (abs (rf K* (- N 1))) epsilon10))
       ;Use the scaled form of the recurrence if the value of K at s is non-zero
       (define tt (- (/ pv kv)))
       (s! K* 0 (rf qp* 0))
       (for ([i (in-range 1 N)])(s! K* i (+ (* tt (rf qk* (- i 1))) (rf qp* i))))]
      [else ;Use unscaled form
       (s! K* 0 0.0)
       (for ([i (in-range 1 N)])(s! K* i (rf qk* (- i 1))))])
    (set! kv (rf K* 0))
    (for ([i (in-range 1 N)])(set! kv (+ (* kv s) (rf K* i))))
    (set! t (if (> (abs kv) (* (abs (rf K* (- N 1))) epsilon10)) (- (/ pv kv)) 0))
    (set! s (+ s t))))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT N NZ* uu vv szr* szi* lzr* lzi* qp* NN a* b* p qk* a1* a3* a7* c* d* e* f* g* h* K*)
  (s! NZ* 0);Numbers of zeros found
  (define tFlag 'undefined)
  (define u uu);uu and vv are coefficients of the starting quadratic
  (define v vv)
  (define relstp 0);initialize remove warning
  (define omp 0);initialize remove warning
  (define ui* (box 'undefined))(define vi* (box 'undefined))
  (define triedFlag #f)
  (for/fold ([j 1])
            ([_ (in-naturals 1)])
    (Quad 1 u v szr* szi* lzr* lzi*)
    ;Return if the roots of the quadratic are real and not close
    ;to multiple or nearly equal and of opposite sign
    #:break (> (- (abs (rf szr*))(abs (rf lzr*))) (* 0.01 (abs (rf lzr*))))
    ;Evaluate polynomial by quadratic synthetic division
    (QuadraticSyntheticDivision NN u v p qp* a* b*)
    (define mp (+ (abs (- (rf a*) (* (rf szr*) (rf b*)))) (abs (* (rf szi*) (rf b*)))))
    ;Compute a rigorous bound on the rounding error in evaluating p
    (define zm (sqrt (abs v)))
    (define ee (* 2 (abs (rf qp* 0))))
    (define t (- (* (rf szr*)(rf b*))))
    (for ([i (in-range 1 N)])(set! ee (+ (* ee zm) (abs (rf qp* i)))))
    (set! ee (+ (* ee zm) (abs (+ (rf a*) t))))
    (set! ee (* (+ (* 9 ee)(* 2 (abs t))(* -7 (+ (abs (+ (rf a*) t))(* zm (abs (rf b*)))))) epsilon.0))
    ;Iteration has converged sufficiently if the polynomial
    ;value is less than 20 times this bound
    #:break (and (<= mp (* 20 ee)) (s! NZ* 2))
    ;Stop iteration after 20 steps
    #:break (> j 10)
    (when (and (>= j 2)
               (<= relstp 0.01) (>= mp omp) (not triedFlag))
      ;A cluster appears to be stalling the convergence.
      ;Five fixed shift steps are taken with a u, v close to the cluster
      (set! relstp (if (< relstp epsilon.0) (sqrt epsilon.0) (sqrt relstp)))
      (set! u (- u (* u relstp)))
      (set! v (+ v (* u relstp)))
      (QuadraticSyntheticDivision NN u v p qp* a* b*)
      (for ([i (in-range 5)])
        (set! tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
        (nextK N tFlag (rf a*) (rf b*) (rf a1*) a3* a7* K* (rf qk*) (rf qp*)))
      (set! triedFlag #t)
      (set! j 0))
    (set! omp mp)
    ;Calculate next K polynomial and new u and v
    (set! tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
    (nextK N tFlag (rf a*) (rf b*) (rf a1*) a3* a7* K* (rf qk*) (rf qp*))
    (set! tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
    (newest tFlag ui* vi* (rf a*) (rf a1*) (rf a3*) (rf a7*) (rf b*) (rf c*) (rf d*) (rf f*) (rf g*) (rf h*) u v (rf K*) N p)
    ;If vi is zero, the iteration is not converging
    (when (not (isZero (rf vi*)))
      (set! relstp (abs (/ (- (rf vi*) v)(rf vi*))))
      (set! u (rf ui*))
      (set! v (rf vi*)))
    #:break (isZero (rf vi*))
    j)
  1)

(define (FixedShift L2 sr v K* N p* NN qp* lzi* lzr* szi* szr*)
(println (list 'FixedShift L2 sr v K* N p* NN qp* lzi* lzr* szi* szr*))
  (call/ec
   (λ (return)
     (define qk* (make-vector (+ N 1) 0))(define svk* (make-vector (+ N 1) 0))
     (define iFlag* (box 1))
     (define NZ* (box 0))
     (define betav 0.25)
     (define betas 0.25)
     (define u (* -2 sr))
     (define oss sr)
     (define ovv v)
     ;Evaluate polynomial by synthetic division
     (define a* (box 'undefined))(define b* (box 'undefined))
     (QuadraticSyntheticDivision NN u v (rf p*) qp* a* b*)
(printf "a&b: ~a ~a\n" (rf a*)(rf b*))
     (define a1* (box 'undefined))(define a3* (box 'undefined))(define a7* (box 'undefined))(define c* (box 'undefined))(define d* (box 'undefined))(define e* (box 'undefined))(define f* (box 'undefined))(define g* (box 'undefined))(define h* (box 'undefined))
     (define tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
     (define otv 0)
     (define ots 0)
     (for ([j (in-range L2)])
       (define fflag 1)
       ;Calculate next K polynomial and estimate v
       (nextK N tFlag (rf a*) (rf b*) (rf a1*) a3* a7* K* (rf qk*) (rf qp*))
       (set! tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
       (define ui* (box 'undefined))(define vi* (box 'undefined))
       (newest tFlag ui* vi* (rf a*) (rf a1*) (rf a3*) (rf a7*) (rf b*) (rf c*) (rf d*) (rf f*) (rf g*) (rf h*) u v (rf K*) N (rf p*))
       (define vv (rf vi*))
       ;Estimate s
       (define ss (if (not (= (rf K* (- N 1)) 0)) (- (/ (rf p* N)(rf K* (- N 1)))) 0.0))
       (define ts 1.0)
       (define tv 1.0)
       (when (and (not (= j 0)) (not (= tFlag 3)))
         ; Compute relative measures of convergence of s and v sequences
         (set! tv (if (not (= vv 0.0)) (abs (/ (- vv ovv) vv)) tv))
         (set! ts (if (not (= ss 0.0)) (abs (/ (- ss oss) ss)) ts))
         ;If decreasing, multiply the two most recent convergence measures
         (define tvv (if (< tv otv) (* tv otv) 1))
         (define tss (if (< ts ots) (* ts ots) 1))
         ;Compare with convergence criteria
         (define vpass (< tvv betav))
         (define spass (< tss betas))
         (when (or spass vpass)
           ;At least one sequence has passed the convergence test.
           ;Store variables before iterating
           (for ([i (in-range N)])(s! svk* i (rf K* i)))
           (define s ss)
           ;Choose iteration according to the fastest converging sequence
           (define stry #f)
           (define vtry #f)
           (let loop ()
             (define continue #f)
             (cond
               [(and (and fflag (set! fflag 0))
                     (and spass (or (not vpass) (< tss tvv))))
                ;Do nothing. Provides a quick short circuit
                ]
               [else
                (QuadIT N NZ* (rf ui*) (rf vi*) szr* szi* lzr* lzi* qp* NN a* b* (rf p*) qk* a1* a3* a7* c* d* e* f* g* h* K*)
                (when (> (rf NZ*) 0)(return (rf NZ*)))
                ;Quadratic iteration has failed. Flag that it has been
                ;tried and decrease the convergence criteriong
                (s! iFlag* 1)(set! vtry #t)
                (set! betav (* betav 0.25))
                ;Try linear iteration if it has not been tried and the s sequence is converging
                (cond
                  [(or stry (not spass))(s! iFlag* 0)]
                  [else (for ([i (in-range N)])(s! K* i (rf svk* i)))])])
             (when (not (= (rf iFlag*) 0))
               (define sss* (box s))
               (RealIT iFlag* NZ* sss* N (rf p*) NN qp* szr* szi* K* qk*)
               (set! s (rf sss*))
               (when (> (rf NZ*) 0)(return (rf NZ*)))
               ;Linear iteration has failed. Flag that it has been
               ;tried and decrease the convergence criterion
               (set! stry #t)
               (set! betas (* betas 0.25))
               (when (not (= (rf iFlag*) 0))
                 ;If linear iteration signals an almost double real zero,
                 ;attempt quadratic iteration
                 (s! ui* (- (+ s s)))
                 (s! vi* (* s s))
                 (set! continue #t)))
             (cond
               [continue (loop)]
               [else
                ;Restore variables
                (for ([i (in-range N)])(s! K* i (rf svk* i)))
                ;Try quadratic iteration if it has not been tried
                ;and the v sequence is converging
                (unless (or (not vpass) vtry) (loop));was break statement
                ]))
           ;Re-compute qp and scalar values to continue the second stage
           (QuadraticSyntheticDivision NN u v (rf p*) qp* a* b*)
           (set! tFlag (calcSC N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))))
       (set! ovv vv)
       (set! oss ss)
       (set! otv tv)
       (set! ots ts))
     (rf NZ*))))

(define evalPoly
  (case-lambda
    [(x p Degree)
     (define ff (rf p 0))
     (for ([i (in-range 1 (+ Degree 1))]) (set! ff (+ (* ff x) (rf p i))))
     ff]
    [(x p Degree f* df*)
     (s! df* (rf p 0))(s! f* (rf p 0))
     (for ([i (in-range 1 Degree)])
       (s! f* (+ (* x (rf f*)) (rf p i)))
       (s! df* (+ (* x (rf df*)) (rf f*))))
     (s! f* (+ (* x (rf f*)) (rf p Degree)))]))

; Scale if there are large or very small coefficients
; Computes a scale factor to multiply the coefficients of the polynomial.
; The scaling is done to avoid overflow and to avoid undetected underflow 
; interfering with the convergence criterion.
; The factor is a power of the base.
(define (scalePoly p* N)
; double ldexp(double x, int n)
; The ldexp() functions multiply x by 2 to the power n.
;
; double frexp(double value, int *exp);
; The frexp() functions break the floating-point number value into
; a normalized fraction and an integral power of 2.
; They store the integer in the int object pointed to by exp.
; The functions return a number x such that x has a magnitude in 
; the interval [1/2, 1) or 0, and value = x*(2**exp).
  'not-implemented)

;Compute lower bound on moduli of zeros
(define (lowerBoundZeroPoly p N)
  (define pt (make-vector (+ N 1) 0))
  (for ([i (in-range N)])(s! pt i (abs (rf p i))))
  (s! pt N (- (abs (rf p N))))
  ;Compute upper estimate of bound
  (define x (exp (/ (- (log (- (rf pt N))) (log (rf pt 0))) N)))
  (when (not (isZero (rf pt (- N 1))));If Newton step at the origin is better, use it
    (define xm (- (/ (rf pt N)(rf pt (- N 1)))))
    (when (< xm x)(set! x xm)))
  ;Chop the interval (0, x) until f<=0
  (define xm x)
  (for ([_ (in-naturals)]
        #:break (< (evalPoly xm pt N) 0))
    (set! x xm)(set! xm (* 0.1 x)))
  ;Do Newton iteration until x converges to two decimal places
  (define dx 'undefined)
  (for ([_ (in-naturals)])
    (define f* (box 'undefined))(define df* (box 'undefined))
    (evalPoly x pt N f* df*)
    (set! dx (/ (rf f*)(rf df*)))
    (set! x (- x dx))
    #:break (<= (abs dx) (* (abs x) .005))
    'dummy)
  x)

(define (roots2 p Degree j zeror* zeroi*)
  (cond
    [(= Degree 1)
     (s! zeror* j (- (/ (rf p 1) (rf p 0))))
     (s! zeroi* j 0)]
    [(= Degree 2)
     (define szr* (box 'undefined))(define szi* (box 'undefined))(define lzr* (box 'undefined))(define lzi* (box 'undefined))
     (Quad (rf p 0) (rf p 1) (rf p 2) szr* szi* lzr* lzi*)
     (s! zeror* j (rf szr*))      (s! zeroi* j (rf szi*))
     (s! zeror* (+ j 1) (rf lzr*))(s! zeroi* (+ j 1) (rf lzi*))]))

(define (roots op Degree zeror* zeroi*)
  (call/ec
   (λ (return)
     (when (< Degree 1) (return 'degree<1))
     ;Do a quick check to see if leading coefficient is 0
     ;The leading coefficient is zero. No further action is taken. Program terminated
     (when (isZero (rf op 0)) (return 'leading-zero))
     (define K* (make-vector (+ Degree 1) 0))
     (define p* (make-vector (+ Degree 1) 0))
     (define qp* (make-vector (+ Degree 1) 0))
     (define temp* (make-vector (+ Degree 1) 0))

     (define N Degree)
     (define xx (sqrt 0.5))
     (define yy (- xx))
     ;Remove zeros at the origin, if any
     (for ([j (in-range N)])
       #:break (not (isZero (rf op N)))
       (set! N (- N 1))(s! zeror* j 0.0)(s! zeroi* j 0.0))
     (for ([i (in-range (+ N 1))])(s! p* i (rf op i)));make a copy of the coefficients
     (for ([_ (in-naturals)])
       #:break (not (> N 0))
       ;Main loop
       ;Start the algorithm for one zero
       #:break (and (< N 3) (roots2 (rf p*) N (- Degree N) zeror* zeroi*))
       ;Find the largest and smallest moduli of the coefficients !!this is imediatly scaling, not just finding
       (scalePoly p* N)
       ;Compute lower bound on moduli of zeros
       (define bnd (lowerBoundZeroPoly (rf p*) N))
       ;Compute the derivative as the initial K polynomial and
       ;do 5 steps with no shift
       (for ([i (in-range 1 N)]) (s! K* i (/ (* (- N i) (rf p* i)) N)))
       (s! K* 0 (rf p* 0))
       (define NM1 (- N 1))
       (define aa (rf p* N))
       (define bb (rf p* NM1))
       (define zerok (isZero (rf K* NM1)))
       (for ([iter (in-range 5)])
         (cond
           [zerok ;Use unscaled form of recurrence
            (for ([i (in-range NM1)])(s! K* (- NM1 i) (rf K* (- NM1 i 1))))
            (s! K* 0 0)
            (set! zerok (isZero (rf K* NM1)))
            ]
           [else ;Use scaled form of recurrence if value of K at 0 is nonzero
            (define t (- (/ aa (rf K* NM1))))
            (for ([i (in-range NM1)])
              (define j (- NM1 i))
              (s! K* j (+ (* t (rf K* (- j 1))) (rf p* j))))
            (s! K* 0 (rf p* 0))
            (set! zerok (<= (abs (rf K* NM1)) (* (abs bb) epsilon10)))]))
(printf "Zero shift finished\n")
(println K*)
(printf "bound: ~a\n" bnd)
       ;Save K for restarts with new shifts
       (for ([i (in-range N)])(s! temp* i (rf K* i)))
       ;Loop to select the quadratic corresponding to each new shift
       (define ok #f)
       (for ([iter (in-range 20)]
             #:break ok)
         ;Quadratic corresponds to a double shift to a non-real point and its
         ;complex conjugate. The point has modules BND and amplitude rotated
         ;by 94° from the previous shift
         (define tmp (+ (* -1 sinr yy)(* cosr xx)))
         (set! yy (+ (* sinr xx)(* cosr yy)))
         (set! xx tmp)
         (define sr (* bnd xx))
         ;Second stage calculation fixed quadratic
         (define lzi* (box 'undefined))(define lzr* (box 'undefined))(define szi* (box 'undefined))(define szr* (box 'undefined))
         (define NZ (FixedShift (* 20 (+ iter 1)) sr bnd K* N p* (+ N 1) qp* lzi* lzr* szi* szr*))
         (set! ok (not (= NZ 0)))
         (cond
           [ok
            ;The second stage jumps directly to one of the third stage iterations and
            ;returns here if successful.Deflate the polynomial, store the zero or
            ;zeros, and return to the main algorithm.
            (define j (- Degree N))
            (s! zeror* j (rf szr*))
            (s! zeroi* j (rf szi*))
            (when (not (= NZ 1))
              (s! zeror* (+ j 1) (rf lzr*))
              (s! zeroi* (+ j 1) (rf lzi*)))
            (set! N (- N NZ))
            (for ([i (in-range (+ N 1))]) (s! p* i (rf qp* i)))]
           [else
            ;If the iteration is unseccessful, another quadratic is chosen after restoring K
            (for ([i (in-range N)])(s! K* i (rf temp* i)))]))
       ;Return with failure if no convergence with 20 shifts
       (when (not ok) (return 'no-fixed-shift-convergence)))
     0)))
(define (mfr p)
  (define degree (- (vector-length p) 1))
  (define zeror* (make-vector degree 0))(define zeroi* (make-vector degree 0))
  (roots p degree zeror* zeroi*)
  (for/list ([i (in-range degree)])
    (+ (rf zeror* i)(* +i (rf zeroi* i)))))
(module+ test
  ;(mfr #(1. 2. 3. 4. -5.))
  ;(mfr #(1. 3. 1. 0.08866210790363471))
  ;irritatingly difficult (flpoly-from-roots .9998 .9999 1. 1.003 1.003
  ;(mfr #(1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
  ;same but exact
  ;(mfr #(1 -50057/10000 501140361/50000000 -501711082871/50000000000 251141082742009/50000000000000 -50285360871009/50000000000000))
  (mfr #(1e-8 1e-16 1e-20 -1e25 38.5))
  )