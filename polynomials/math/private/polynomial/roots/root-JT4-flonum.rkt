#lang racket/base

#|
based on the original fortran & cpp translation fromTOMS/493 found at http://www.akiti.ca/PolyRootRe.html
|#

(require math/flonum math/bigfloat
         racket/math
         racket/match
         racket/vector)
(require (for-syntax racket/base))
(define (make-dd f1 f2)
  (λ (a b)
    (cond
      [(and (pair? a)(pair? b))(define-values (c d)(f1 (car a)(cdr a)(car b)(cdr b)))(cons c d)]
      [(pair? a)(define-values (c d)(f1 (car a)(cdr a)b))(cons c d)]
      [(pair? b)(define-values (c d)(f1 (car b)(cdr b)a))(cons c d)]
      [else (define-values (c d)(f2 a b))(cons c d)])))
(define (make-bf f1)
  (λ (a b)
    (cond
      [(and (bigfloat? a) (bigfloat? b))(f1 a b)]
      [(bigfloat? a) (f1 a (bf b))]
      [(bigfloat? b) (f1 (bf a) b)]
      [else (f1 (bf a) (bf b))])))
(define dd+ +)(define dd* *)(define dd/ /)(define dd- -)(define dd->fl values)
;(define dd+ fl+)(define dd* fl*)(define dd/ fl/)(define dd- fl-)(define dd->fl values)
;(define dd+ (make-dd fl2+ fl+/error))(define dd* (make-dd fl2* fl*/error))(define dd/ (make-dd fl2/ fl//error))(define dd- (make-dd fl2- fl-/error))(define (dd->fl a)(car a));
;(define dd+ (make-bf bf+))(define dd* (make-bf bf*))(define dd/ (make-bf bf/))(define dd- (make-bf bf-))(define dd->fl bigfloat->flonum)(bf-precision 1024)
;same with extfl...
(define (in-rng-nr? N)(not (or (nan? N)(infinite? N))))


(define-syntax label
  (let ()
    (define L '())
    (define ALL '(Quad-1 Quad-2 Quad-3.1.1 Quad-3.1.1.1 Quad-3.1.1.2 Quad-3.1.2.1  Quad-3.1.2.2 Quad-3.2.1 Quad-3.2.2.1.1 Quad-3.2.2.1.2 Quad-3.2.2.2.1 Quad-3.2.2.2.2
                  QuadraticSyntheticDivision
                  calcSC-type3 calcSC-type2 calcSC-type1
                  nextK-type3 nextK-normal nextK-smalla1
                  newest-type3 newest-type2 newest-type1 newest-temp0 newest-normal
                  RealIT-converged RealIT-maxiter RealIT-zero-cluster RealIT-scaled RealIT-unscaled
                  QuadIT-maxiter QuadIT-go-linear QuadIT-converged QuadIT-relstp QuadIT-norelstp QuadIT-nonconverging QuadIT-normal
                  FixedShift-maxiter FixedShift-pass0-or-factor FixedShift-nonconvergingpass FixedShift-LinFirst FixedShift-QuadFirst FixedShift-QuadConverged
                  FixedShift-LinSecond FixedShift-LinConverged FixedShift-QuadSecondSpec FixedShift-QuadSecondNorm FixedShift-QuadOver FixedShift-LinOver
                  ZeroShift-unscaled ZeroShift-scaled
                  1root-maxiter 1root-rootfound 1root-nexttry
                  roots-degree1 roots-leadingzero roots-s@0 roots-onlyZeroes roots-roots2 roots-maxiter
                  scaleP-scalable scaleP-unscalable scaleP-not-scaled scaleP-scaled
                  LBZP-newtonstep LBZP-converged LBZP-loop))
    #;(define S '(Quad-3.2.2.2.1 Quad-1 Quad-2 Quad-3.1.2.1 Quad-3.2.2.2.1
                calcSC-type3 nextK-type3 nextK-smalla1 newest-type3 RealIT-unscaled))
    (define S '())
    (λ (stx)
      (syntax-case stx ()
        [(_ x)
         (cond
           [(equal? (syntax-e #'x) 'show)
            (with-syntax ([lst (datum->syntax stx L)])
              #'(println 'lst))]
           [(member (syntax-e #'x) S)   #'(println 'x)]
           [else
            (when (member (syntax-e #'x) L) (printf "Double entry ~a\n" (syntax-e #'x)))
            (set! L (cons (syntax-e #'x) L))
            (when (not (member (syntax-e #'x) ALL))(printf "New entry ~a\n" (syntax-e #'x)))
            #'(void)])]))))
;(define-syntax-rule (TEST body ...) (void '(module+ test body ...)))
(define-syntax-rule (TEST body ...) (module+ test body ...))

(module+ test (require rackunit))

(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))
(define +FLT_MIN (floating-point-bytes->real (bytes #b00000000 #b00000000 #b00000000 #b00000001)))
(define +FLT_MAX (floating-point-bytes->real (bytes #b11111111 #b11111111 #b11111111 #b01111110)))

(define RADFAC (/ (angle -1) 180));Degrees - to - radians conversion factor = pi/180

(define s!
  (case-lambda [(a b)
                (if (and (vector? a)(vector? b))
                    (for ([i (in-range (vector-length a))])(vector-set! a i (vector-ref b i)))
                    (set-box! a b))]
               [(a b c)
                (if (and (vector? a)(vector? b))
                    (for ([i (in-range c)])(vector-set! a i (vector-ref b i)))
                    (vector-set! a b c))]))
(define rf
  (case-lambda [(a)
                (if (vector? a)
                    (vector->immutable-vector a)
                    (unbox a))]
               [(a b)(vector-ref a b)]))

(define-syntax (prepare-one stx)
  (syntax-case stx (*)
    [(_ (id *)) #'(define id (box 'undefined))]
    [(_ (id nr *)) #'(define id (make-vector nr 0.0))]
    [(_ (id nr)) #'(define id (box nr))]
    [(_ (id nr v)) #'(define id (make-vector nr v))]))
(define-syntax (prepare stx)
  (syntax-case stx ()
    [(_ ids ...) #'(begin (prepare-one ids) ...)]))

; CALCULATE THE ZEROS OF THE QUADRATIC A*Z**2+B1*Z+C.
; THE QUADRATIC FORMULA, MODIFIED TO AVOID
; OVERFLOW, IS USED TO FIND THE LARGER ZERO IF THE
; ZEROS ARE REAL AND BOTH ZEROS ARE COMPLEX.
; THE SMALLER REAL ZERO IS FOUND DIRECTLY FROM THE
; PRODUCT OF THE ZEROS C/A.
(define (Quad a2 a1 a0)
  (cond
    [(= a2 0)(label Quad-1) (raise-argument-error 'Quad "not a quadratic" 0 a2 a1 a0)]
    [(= a0 0)(label Quad-2) `((0.0 . 0.0) (,(- (/ a1 a2)) . 0.0))]
    ;what if a2/a1/a0 ±inf.0
    [else
     (define a1/2 (/ a1 2))
     (define-values (D* E*)
       (cond
           [(< (abs a1/2) (abs a0))
            (label Quad-3.1.1)
            (define E0
              (cond
                [(< a0 0)(label Quad-3.1.1.1)(- a2)]
                [else   (label Quad-3.1.1.2)   a2]))
            (define E1 (- (* a1/2 (/ a1/2 (abs a0))) E0))
            (values (* (sqrt (abs E1)) (sqrt (abs a0)))
                    E1)]
           [else
            (define E
              (let ([E (- 1 (* (/ a2 a1/2)(/ a0 a1/2)))])
                (cond
                  [(in-rng-nr? E)(label Quad-3.1.2.2) E]
                  [else (label Quad-3.1.2.1) (- 1 (/ (* a2 a0) a1/2 a1/2))])))
            (values (* (sqrt (abs E))(abs a1/2))
                    E)]))
     ;compute Discriminant avoiding overflow
     (cond
       [(< E* 0)
        (label Quad-3.2.1)
        ;comples conjugate zeros
        (define R (- (/ a1/2 a2)))
        (define I (abs (/ D* a2)))
        (list (cons R I) (cons R (- I)))]
       [else
        ;real zeros
        (define D** (cond [(> a1/2 0)(label Quad-3.2.2.1.1)(- D*)][else(label Quad-3.2.2.1.2)D*]))
        (define Z1 (/ (- D** a1/2) a2))
        (cond
          [(= Z1 0) (label Quad-3.2.2.2.1)'((0.0 . 0.0) (0.0 . 0.0))]
          [else     (label Quad-3.2.2.2.2)`((,(/ (/ a0 Z1) a2) . 0.0) (,Z1 . 0.0))])])]))
(TEST
  (check-exn exn:fail:contract? (λ ()(Quad 0 0 0)))
  ;(check-within (Quad 0 0 1) '(0 0 0 0) epsilon100)
  ;(check-within (Quad 0 1 0) '(0 0 0 0) epsilon100)
  ;(check-within (Quad 0 1 1) '(-1 0 0 0) epsilon100)
  (check-within (Quad 1 0 0) '((0 . 0) (0 . 0)) epsilon100)
  (check-within (Quad 1 0 1) '((0 . 1) (0 . -1)) epsilon100)
  (check-within (Quad 1 0 -1) '((-1 . 0) (1 . 0)) epsilon100)
  (check-within (Quad 1 1 0) '((0 . 0) (-1 . 0)) epsilon100)
  (check-within (Quad 1 6 3) '((-0.5505102572168219 . 0)  (-5.449489742783178 .  0)) epsilon100)
  (check-within (Quad 1 2 3) '((-1 . 1.414213562373095)   (-1 . -1.414213562373095)) epsilon100)
  (check-within (Quad 1 6 7) '((-1.585786437626905 . 0)   (-4.414213562373095 . 0)) epsilon100)
  (check-within (Quad +max.0 0.9 -min.0) '((0.0 . 0.0) (0.0 . 0.0)) epsilon100)
  (check-equal? (Quad +inf.0 1e10 -9e-303) '((+nan.0 . 0.0) (+nan.0 . 0.0))))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision P u v)
  (define NN (vector-length P))
  (label QuadraticSyntheticDivision)
  (define q (make-vector NN 0.0))
  (define b (rf P 0))
  (s! q 0 b)
  (define a (- (rf P 1) (* b u)))
  (s! q 1 a)
  (for ([i (in-range 2 NN)])
    (s! q i (- (rf P i) (+ (* a u)(* b v))))
    (set! b a)
    (set! a (rf q i)))
  (list q a b))
(TEST
  (check-within (QuadraticSyntheticDivision #(1. 2. 3. 4.) 2.8 3.5)
                (list #(1.0 -0.8 1.74 1.928) 1.928 1.74)
                epsilon100)
  (check-within (QuadraticSyntheticDivision #(0.428 3.62 2.6e-4 12. 0.005) 3.345 6.482)
                (list #(0.428 2.18834 -10.0940333 31.5797215085 -40.199644595332494)
                      -40.199644595332494 31.5797215085)
                epsilon100))

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
(define (calcSC K a b u v)
  (define N (vector-length K))
  ;Synthetic division of K by the quadratic 1, u, v
  (match-define (list qk* c d)(QuadraticSyntheticDivision K u v))
  (cond
    [(and (<= (abs c) (* epsilon100 (abs (rf K (- N 1)))))
          (<= (abs d) (* epsilon100 (abs (rf K (- N 2))))))
     (label calcSC-type3)
     ;type=3 indicates the quadratic is almost a factor of K
     (list 'calcSC:almost-factor qk* c d)]
    [else
     (define h (* v b))
     (cond
       [(>= (abs d) (abs c))
        (label calcSC-type2)
        ;TYPE = 2 indicates that all formulas are divided by d
        (define e (/ a d))
        (define f (/ c d))
        (define g (* u b))
        (define a1 (- (* f b) a))
        (define a3 (+ (* e (+ g a)) (* h (/ b d))))
        (define a7 (+ h (* (+ f u) a)))
        (list 'calcSC:div-by-d qk* c d e f g h a1 a3 a7)]
       [else
        (label calcSC-type1)
        ;TYPE = 1 indicates that all formulas are divided by c
        (define e (/ a c))
        (define f (/ d c))
        (define g (* e u))
        (define a1 (- b (* a (/ d c))))
        (define a3 (+ (* e a) (* (+ g (/ h c)) b)))
        (define a7 (+ (* g d) (* h f) a))
        (list 'calcSC:div-by-c qk* c d e f g h a1 a3 a7)])]))
(TEST
  (check-within (calcSC #(1. 2. 3. 4.) 2.3 4.6 1.8 9.2)
                (list 'calcSC:div-by-c
                      #(1.0 0.2 -6.56 13.968)
                      13.968 -6.56 0.16466208476517755 -0.46964490263459335 0.2963917525773196 42.32
                      5.680183276059564 15.679123711340203 -19.519702176403204)
                epsilon100)
  (check-within (calcSC #(1. -10 35. -50.) 2.3 4.6 -6. 8.)
                (list 'calcSC:div-by-d
                      #(1.0 -4.0 3.0 0.0)
                      0.0 3.0 0.7666666666666666 0.0 -27.6 36.8
                      -2.3 37.03 23.0)
                epsilon100)
  (check-within (calcSC #(1. -10 35. -50. 24.) 2.3 4.6 -6. 8.00000000000001)
                (list 'calcSC:almost-factor
                      #(1.0 -4.0 2.999999999999986 -4.263256414560601e-14 -1.7408297026122455e-13)
                      -1.7408297026122455e-13 -4.263256414560601e-14)
                epsilon100))

;Computes the next K polynomials using the scalars computed in calcSC
(define (nextK qp qk tFlag a b a1 a3 a7)
  (define N (vector-length qk))
  (define K (make-vector N 0.0))
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     (label nextK-type3)
     ; use unscaled form of the recurrence
     (for ([i (in-range 2 N)])(s! K i (rf qk (- i 2))))
     (list K a3 a7)]
    [else
     (define temp (if (equal? tFlag 'calcSC:div-by-c) b a))
     (cond
       [(> (abs a1) (* epsilon10 (abs temp)))
        (label nextK-normal)
        (define a7+ (/ a7 a1))
        (define a3+ (/ a3 a1))
        (s! K 0 (rf qp 0))
        (s! K 1 (- (rf qp 1) (* a7+ (rf qp 0))))
        (for ([i (in-range 2 N)])
          (s! K i (+ (rf qp i) (* -1 a7+ (rf qp (- i 1))) (* a3+ (rf qk (- i 2))))))
        (list K a3+ a7+)]
       [else
        (label nextK-smalla1)
        ;If a1 is nearly zero, then use a special form of the recurrence
        (s! K 0 0)
        (s! K 1 (* -1 a7 (rf qp 0)))
        (for ([i (in-range 2 N)])
          (s! K i (+ (* a3 (rf qk (- i 2))) (* -1 a7 (rf qp (- i 1))))))
        (list K a3 a7)])]))
(TEST
  (check-within (nextK #(16. 17. 18. 19. 20.) #(11. 12. 13. 14.) 'calcSC:div-by-c 8. 9. 10. 6. 7.)
                (list #(16.0 5.8 12.7 13.6) .6 .7)
                epsilon100)
  (check-within (nextK #(16. 17. 18. 19. 20.) #(11. 12. 13. 14.) 'calcSC:div-by-c 8. 9. 0. 6. 7.)
                (list #(0 -112. -53. -54.) 6. 7.)
                epsilon100)
  (check-within (nextK #(16. 17. 18. 19. 20.) #(11. 12. 13. 14.) 'calcSC:almost-factor 8. 9. 10. 6. 7.)
                (list #(0 0 11. 12.) 6. 7.)
                epsilon100))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest P K tFlag a a1 a3 a7 b c d f g h u v)
  (define N (vector-length K))
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     (label newest-type3)
     (list 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (cond
         [(not (equal? tFlag 'calcSC:div-by-d))
          (label newest-type2)
          (values (dd+ (dd+ a (dd* u b)) (dd* h f))
                  (dd+ c (dd* (dd+ u (dd* v f)) d)))]
         [else
          (label newest-type1)
          (values (dd+ (dd* (dd+ a g) f) h)
                  (dd+ (dd* (dd+ f u) c) (dd* v d)))]))

     (define b1 (dd* -1.0 (dd/ (rf K (- N 1))(rf P N))))
     (define b2 (dd* -1.0 (dd/ (dd+ (rf K (- N 2)) (dd* b1 (rf P (- N 1)))) (rf P N))))
     (define c1 (dd* (dd* v b2) a1))
     (define c2 (dd* b1 a7))
     (define c3 (dd* (dd* b1 b1) a3))
     (define c4 (dd+ (dd* -1.0 (dd+ c2 c3)) c1))
     (define temp (dd+ (dd- a5 c4) (dd* b1 a4)))
     (cond
       [(= (dd->fl temp) 0.0)
        (label newest-temp0)
        (list 0.0 0.0)]
       ;!!!it temp ≈ 0.0 these values blow up. Is this a good idea?
       [else
        (label newest-normal)
        (let ();([a4 (dd->fl a4)][a5 (dd->fl a5)][b1 (dd->fl b1)][b2 (dd->fl b2)][c1 (dd->fl c1)][c2 (dd->fl c2)][c3 (dd->fl c3)][c4 (dd->fl c4)][temp (dd->fl temp)])
          (list (dd->fl (dd+ (dd* -1.0 (dd/ (dd+ (dd* u (dd+ c3 c2)) (dd* v (dd+ (dd* b1 a1)(dd* b2 a7)))) temp)) u))
                (dd->fl (dd* v (dd+ 1.0 (dd/ c4 temp))))))])]))
(TEST
  ;tflag=3
  (check-within (newest #(18. 19. 20. 21. 22.) #(13. 14. 15. 16.) 'calcSC:almost-factor 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12.)
                '(0. 0.) epsilon100)
  ;tflag=2 & temp=0
  (check-within (newest #(18. 19. 20. 21. 22.) #(13. 14. 15. 16.) 'calcSC:div-by-d 1. 2. 3. 4. 5. -0.8908220965637230 7. 8. 9. 10. 11. 12.)
                '(0. 0.) epsilon100)
  ;tflag=2 & temp!=0
  (check-within (newest #(18. 19. 20. 21. 22.) #(13. 14. 15. 16.) 'calcSC:div-by-d 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12.)
                '(11.239868703446534 12.148466102764804) epsilon100)
  ;tflag=1 & temp=0
  (check-within (newest #(18. 19. 20. 21. 22.) #(13. 14. 15. 16.) 'calcSC:div-by-c 1. 2. 3. 4. 5. 100.52892561983471 0. 8. 9. 10. 11. 12.)
                '(0. 0.) epsilon100)
  ;tflag=1 & temp!=0
  (check-within (newest #(18. 19. 20. 21. 22.) #(13. 14. 15. 16.) 'calcSC:div-by-c 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12.)
                '(11.047985250849212 12.029700344736144) epsilon100)
  ;general accuracy
  (check-within (newest #(765.85527498437887 -1347.293632350993 -2161.1901804835061 -7837.7065086597486 -3083.5325907341339 2512.6246767498906 5888.8148218838123 -224.71114833786896 4321.6465771244393 -4104.5415694069588 -358.02596267509489 -5940.1714091583599 -2813.1556404590783 -1218.7896752219331 -92.316085769292613 13.465814510071247 )
                        #(765.85527498437887 569.21989433594013 -70.015121432447586 -702.31273591596982 -9385.9870113488287 7161.0962876975536 -6.3514328002929688 2149.7078857421875 2603.109375 -6064. -80480. 4108288. 128712704. -11601444864. -569620037632.)
                        'calcSC:div-by-c 4.2070203373260126e+029 -1.2702606492846791e+028 -4.8274289306750895e+031 1.2166940450248765e+029 -5.2749842363542267e+027 -5.5170988810118383e+027 -9.7406057385308503e+025 0.017655303899038365 -539.9094138852181 -1.9916002499454986e+031 7.080387980931846 3775.5567802833493)
                '(3.7978598044219325e-10 -5.868394095550277e-11) epsilon100))
(define (calcSC->nextK qp K a b u v)
  (match-define (list K* _ _)
    (match (calcSC K a b u v)
      [(list tFlag qk c d)
       (nextK qp qk tFlag a b 0.0 0.0 0.0)]
      [(list tFlag qk c d e f g h a1 a3 a7)
       (nextK qp qk tFlag a b a1 a3 a7)]))
  K*)
(define (calcSC->newest p K a b u v)
  (match (calcSC K a b u v)
    [(list tFlag qk c d)
     (cons tFlag (newest p K tFlag a 0.0 0.0 0.0 b 0.0 0.0 0.0 0.0 0.0 u v))]
    [(list tFlag qk c d e f g h a1 a3 a7)
     (cons tFlag (newest p K tFlag a a1 a3 a7 b c d f g h u v))]))
(define (calcSC->K+newest p qp K a b u v)
  (define K+ (calcSC->nextK qp K a b u v))
  (cons K+ (calcSC->newest p K+ a b u v)))


; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT maxiter p K sss)
  (define NN (vector-length p))
  (define N (vector-length K))
  ;return (list iFlag NZ qp K* qk sss* szr szi)
  (let loop ([j 1]
             [K K]
             [s sss][omp 0][t 0])
    ; Evaluate p at s and compute remainder
    (define qp* (make-vector NN 0.0))
    (define pv (rf p 0))(s! qp* 0 pv)
    (for ([i (in-range 1 NN)])
      (set! pv (+ (* pv s) (rf p i)))(s! qp* i pv))
    (define mp (abs pv))
    ;Compute a rigorous bound on the error in evaluating p
    (define ms (abs s))
    (define ee (for/fold ([ee (* 0.5 (abs (rf qp* 0)))])
                         ([i (in-range 1 NN)])
                 (+ (* ee ms) (abs (rf qp* i)))))
    (cond
      [(<= mp (* 20 epsilon.0 (- (* 2 ee) mp)))
       ;Iteration has converged sufficiently if the polynomial
       ;value is less than 20 times this bound
       (label RealIT-converged)
       (list 'RealIT:normal 1 qp* K sss s)]
      [(> j maxiter)
       (label RealIT-maxiter)
       (list 'RealIT:maxiter 0 qp* K sss 'undefined)]
      [(and (>= j 2)
            (<= (abs t) (* 0.001 (abs (- s t)))) (> mp omp))
       ;A cluster of zeros near the real axis has been encountered;
       ;Return with iFlag set to initiate a quadratic iteration
       (label RealIT-zero-cluster)
       (list 'RealIT:zero-cluster 0 qp* K s 'undefined)]
      [else
       ;Return if the polynomial value has increased significantly
       ;Compute t, the next polynomial and the new iterate
       (define qk* (make-vector N 0.0))
       (define kv (rf K 0))(s! qk* 0 kv)
       (for ([i (in-range 1 N)])
         (set! kv (+ (* kv s) (rf K i)))(s! qk* i kv))
       (define K+
         (cond
           [(> (abs kv) (* (abs (rf K (- N 1))) epsilon10))
            (label RealIT-scaled)
            ;Use the scaled form of the recurrence if the value of K at s is non-zero
            (define tt (- (/ pv kv)))
            (list->vector
             (cons (rf qp* 0)
                   (for/list ([i (in-range 1 N)])(+ (* tt (rf qk* (- i 1))) (rf qp* i)))))]
           [else ;Use unscaled form
            (label RealIT-unscaled)
            (list->vector
             (cons 0.0 (for/list ([i (in-range 1 N)])(rf qk* (- i 1)))))]))
       (define kv+ (evalPoly (vector-copy K+ 0 N) s))
       (define t+ (if (> (abs kv+) (* (abs (rf K+ (- N 1))) epsilon10)) (- (/ pv kv+)) 0))
       (loop (+ j 1) K+ (+ s t+) mp t+)])))
(TEST
  ;break small mp = zero found
 (check-within (RealIT 10 #(1. 2. 3. 4. -5.) #(1. 2. 3. 4.) 0.2)
                (list 'RealIT:normal 1
                      #(1.0 2.68412431945307 4.836274723373266 7.308613153815818 0.0)
                      #(1.0 2.6841243194530695 4.836274723373265 7.308613153815818)
                      0.2 0.6841243194530697)
                epsilon100)
  ;break iterrations j (iFlag=0 & NZ=0)
 (check-within (RealIT 10 #(1. 2. 3. 4. 5.) #(1. 2. 3. 4.) 1.0)
                (list 'RealIT:maxiter 0
                      #(1.0 -0.6849750434472566 4.839140897040084 -8.992972540277597 29.145906837051825)
                      #(1.0 1.0919036572997787 1.0019196569203022 3.933013624211993)
                      1 'undefined)
                epsilon100)
  ;break  cluster of zeros
 (check-within (RealIT 10 #(4.9679877220982345 9.29937913880471 -9.609506455896735 -2.5160214731778163 -6.029809381393797) #(8.514417957281449 0.5198895391395837 -9.66980775616132 0.45524621258751097) 3.5502909446276085)
                (list 'RealIT:zero-cluster 0
                      #(4.9679877220982345 2.2034324874736058 -12.756744383111027 15.70487250861968 -28.461615521215446)
                      #(4.9679877220982345 -6701.697712994184 7942.889509061441 -1976.5039946730667)
                      -1.4283341763844224 'undefined)
                epsilon100)
  ;cond big kv [used in previous tests]
  ;cond else [used at least the first time in next test]
 (check-within (RealIT 10 #(1. 2. 3. 4. -5.) #(1. 2. 3. 0.) 0.0)
                (list 'RealIT:normal 1
                      #(1.0 2.68412431945307 4.836274723373266 7.308613153815818 0.0)
                      #(1.0 2.6841243194530113 4.836274723373138 7.308613153815954)
                      0.0 0.6841243194530697)
                epsilon100))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT maxiter uu vv p K)
  (let loop ([j 0][omp 0][relstp 0][tried? #f]
             ;uu and vv are coefficients of the starting quadratic
             [u uu][v vv]
             [qp (make-vector (vector-length p) 0.0)][K K])
    (match-define (list (cons szr szi)(cons lzr lzi))(Quad 1. u v))
    (cond
      [(> (abs (- (abs szr)(abs lzr))) (* 0.01 (abs lzr)))
       ;Return if the roots of the quadratic are real and not close
       ;to multiple or nearly equal and of opposite sign
       (label QuadIT-go-linear)
       (list 0 qp K szr szi lzr lzi)]
      [else
       ;Evaluate polynomial by quadratic synthetic division
       (match-define (list qp a b)(QuadraticSyntheticDivision p u v))
       (define mp (+ (abs (- a (* szr b))) (abs (* szi b))))
       ;Compute a rigorous bound on the rounding error in evaluating p
       (define zm (sqrt (abs v)))
       (define t (- (* szr b)))
       (define e0 (for/fold ([e0 (* 2 (abs (rf qp 0)))])
                            ([qpi (in-vector qp 1 (vector-length K))])
                    (+ (* e0 zm) (abs qpi))))
       (define ee (* (+ (* 9 (+ (* e0 zm) (abs (+ a t))))
                        (* 2 (abs t))
                        (* -7 (+ (abs (+ a t))(* zm (abs b)))))
                     epsilon.0))
        (cond
         [(<= mp (* 20 ee))
          ;Iteration has converged sufficiently if the polynomial
          ;value is less than 20 times this bound
          (label QuadIT-converged)
          (list 2 qp K szr szi lzr lzi)]
         ;Stop iteration after 20 steps
         [(> j maxiter)
          (label QuadIT-maxiter)
          (list 0 qp K szr szi lzr lzi)]
         [else
          (define-values (j+ tried?+ u+ v+ a+ b+ qp+ K+)
            (cond
              [(and (>= j 2)
                    (<= relstp 0.01) (>= mp omp) (not tried?))
               ;A cluster appears to be stalling the convergence.
               ;Five fixed shift steps are taken with a u, v close to the cluster
               (label QuadIT-relstp)
               (define relstp+ (if (< relstp epsilon.0) (sqrt epsilon.0) (sqrt relstp)))
               (define u+ (- u (* u relstp+)))
               (define v+ (+ v (* v relstp+)))
               (match-define (list qp+ a+ b+)(QuadraticSyntheticDivision p u+ v+))
               (define K+
                 (for/fold ([K+ K])
                           ([i (in-range 5)])
                   (calcSC->nextK qp+ K+ a+ b+ u+ v+)))
               (values 0 #t u+ v+ a+ b+ qp+ K+)]
              [else
               (label QuadIT-norelstp)
               (values j tried? u v a b qp K)]))
          ;Calculate next K polynomial and new u and v
          (match-define (list Ki _ ui vi)(calcSC->K+newest p qp+ K+ a+ b+ u+ v+))
          (cond
            [(= vi 0.0)
             ;If vi is zero, the iteration is not converging
             (label QuadIT-nonconverging)
             (list 0 qp+ Ki szr szi lzr lzi)]
            [else
             (label QuadIT-normal)
             (loop (+ j+ 1) mp (abs (/ (- vi v+)vi)) tried?+
                   ui vi qp+ Ki)])])])))
(TEST
  ;QuadIT-go-linear
  (check-within (QuadIT 20 6. 7. #(1. 2. 3. 4. 5.) #(1. 2. 3. 4.))
                '(0 #(0.0 0.0 0.0 0.0 0.0)
                    #(1. 2. 3. 4.)
                    -1.585786437626905 0 -4.414213562373095 0) epsilon100)
  ;QuadIT-converged
  (check-within (QuadIT 20 -0.575630959115296 0.0828377502729989 #(1. 2. 3. 4. 5.) #(1. 2. 3. 4.))
                '(2 #(1.0 2.575630959115296 2.3944555573388273 0. 0.)
                    #(1.0 2.7141314657388516 2.7511817500546467 0.3316333077843976)
                    0.287815479557648 1.4160930801719076 0.287815479557648 -1.4160930801719076) epsilon100)
  ;QuadIT-maxiter
  ;[TODO ???]
  ;QuadIT-relstp
  (check-within (QuadIT 20 14.737906787890154 56.6995805579966
                        #(-74.43388870038298 -48.684338183687615 82.95039531162064 2.082613677062014 60.82122424869209 -46.15017147716964 61.0180453610964 47.02754709444238 -5.330451975747479 91.51704177156668)
                        #(38.515673952936254 7.252656554000609 -84.42246656861926 31.693388752691646 -27.265410421231138 -35.244767584584565 -97.79006609235279 8.92096535665003 -60.693225828975194))
                '(2 #(-74.43388870038298    28.5525675415266  134.72025177002524 -168.93474867929848   88.79349933216068  46.45222659669343 -84.28416458872897   83.6875414818494   -4.263256414560601e-14 0.0)
                    #(-74.43388870038298 -1291.101631406862   640.9347772344079  2219.5491668571904 -2906.28648822974   1620.6910078684268  739.2772124821581 -1410.6042877693205 1483.7141716555477)
                    -0.5188289035664532 0.907949839624714 -0.5188289035664532 -0.907949839624714)
                epsilon100)
  ;QuadIT-nonconverging
  (check-within (QuadIT 20 7.080387980931846 3775.5567802833493
                        #(765.8552749843789 -1347.293632350993 -2161.190180483506 -7837.706508659749 -3083.532590734134 2512.6246767498906 5888.814821883812 -224.71114833786896 4321.646577124439 -4104.541569406959 -358.0259626750949 -5940.17140915836 -2813.1556404590783 -1218.789675221933 -92.31608576929261 13.465814510071247)
                        #(569.9471955954955 426.1973931512889 -39.26465304820874 -525.558286377151 -6935.288424258491 5283.823600793081 -1.6306656043934709 1584.535288608834 1907.3886808609604 -3739.1601002469033 -430.3641207148028 3278.5379900289245 -1171.8752324055004 1657.6923655682594 -2854.6807003064246))
                '(0 #(765.8552749843789 -1347.2936322007815 -2161.190180771193 -7837.7065090424085 -3083.5325922052557 2512.62467638493 5888.814822470982 -224.71114725974803 4321.646576900171 -4104.541568552454 -358.0259636123816 -5940.171409102984 -2813.1556416132016 -1218.7896755919267 -92.31608592225949 13.465814529259115)
                    #(765.8552749843789 -1235.5810851818474 -2357.715044087775 -8152.951526701866 -4226.790575157413 2062.8408974624554 6255.322322625176 634.2690337473058 4288.868772236702 -3474.158567758887 -956.7406398036304 -5992.395365236808 -3679.6270225980984 -1629.1345512998803 -270.0965405173288)
                    9.806777612197948e-11 5.531679987906852e-06 9.806777612197948e-11 -5.531679987906852e-06)
                epsilon100)
  ;QuadIT-normal [done in break converged]
  )
(define (FixedShift iteration-scheme0 P K sr bnd)
  (define iteration-scheme (if (vector? iteration-scheme0)iteration-scheme0 (make-vector 6 iteration-scheme0)))
  (define N (vector-length K))
  (define u (* -2 sr))
  (define v bnd)
  ;Evaluate polynomial by synthetic division
  (match-define (list qp a b)(QuadraticSyntheticDivision P u v))
  ;fixed shifts: do a fixed shift, if quadratic or linear convergence is detected try to start stage 3.
  ;If unsuccessful continue the fixed shifts
  (let loop ([j 0][K_old K]
             [vv_old v][ss_old sr][tv_old 0][ts_old 0]
             [quadConvergingLimit 0.25][linConvergingLimit 0.25])
    (cond
      [(<= (rf iteration-scheme 3) j) (label FixedShift-maxiter) 'maxiter]
      [else
       ;Calculate next K polynomial and estimate vv
       (match-define (list K tFlag uu vv)(calcSC->K+newest P qp K_old a b u v))
       ;Estimate s
       (define ss (if (= (rf K (- N 1)) 0) 0.0 (- (/ (rf P N)(rf K (- N 1))))))
       (cond
         [(or (= j 0) (equal? tFlag 'calcSC:almost-factor))
          (label FixedShift-pass0-or-factor)
          (loop (+ j 1) K vv ss 1.0 1.0 quadConvergingLimit linConvergingLimit)]
         [else
          ; Compute relative measures of convergence of s and v sequences
          (define tv (if (not (= vv 0.0)) (abs (/ (- vv vv_old) vv)) 1.0))
          (define ts (if (not (= ss 0.0)) (abs (/ (- ss ss_old) ss)) 1.0))
          ;If decreasing, multiply the two most recent convergence measures
          (define tvv (if (< tv tv_old) (* tv tv_old) 1))
          (define tss (if (< ts ts_old) (* ts ts_old) 1))
          ;Compare with convergence criteria
          (define quadConverging? (< tvv quadConvergingLimit))
          (define linConverging? (< tss linConvergingLimit))
          (cond
            [(or linConverging? quadConverging?)
             ;At least one sequence has passed the convergence test.
             (define (tryQuad K ui vi triedLin? quadConvergingLimit linConvergingLimit)
               (match-define (list NZ qp K+ szr szi lzr lzi)(QuadIT (rf iteration-scheme 4) ui vi P K))
               (cond
                 [(= NZ 2)
                  (label FixedShift-QuadConverged)
                  (list (vector-copy qp 0 (- N 1)) (list (+ szr (* +i szi)) (+ lzr (* +i lzi))))]
                 [(= NZ 1) (error 'huh)]
                 [else
                  ;Quadratic iteration has failed, decrease the convergence criterion
                  (define  qCL (* quadConvergingLimit 0.25))
                  (cond
                    [(and (not triedLin?) linConverging?)
                     (label FixedShift-LinSecond)
                     (tryLin ss #t qCL linConvergingLimit)]
                    [else
                     (label FixedShift-QuadOver)
                     (loop (+ j 1) K vv ss tv ts qCL linConvergingLimit)])]))
             (define (tryLin sss triedQuad? quadConvergingLimit linConvergingLimit)
               (match-define (list iFlag NZ qp K+ s szr)(RealIT (rf iteration-scheme 5) P K sss))
               (cond
                 [(= NZ 1)
                  (label FixedShift-LinConverged)
                  (list (vector-copy qp 0 N) (list szr))]
                 [else
                  ;Linear iteration has failed, decrease the convergence criterion
                  (define lCL (* linConvergingLimit 0.25))
                  (cond
                    [(equal? iFlag 'RealIT:zero-cluster)
                     (label FixedShift-QuadSecondSpec)
                     ;If linear iteration signals an almost double real zero, attempt quadratic iteration
                     (tryQuad K+ (* -2 s) (* s s) #t quadConvergingLimit lCL)]
                    [else
                     (cond
                       [(and (not triedQuad?) quadConverging?)
                        (label FixedShift-QuadSecondNorm)
                        (tryQuad K uu vv #t quadConvergingLimit lCL)]
                       [else
                        (label FixedShift-LinOver)
                        (loop (+ j 1) K vv ss tv ts quadConvergingLimit lCL)])])]))
             ;Choose iteration according to the fastest converging sequence, if it fails try the other one (if it is converging)
             (cond
               [(and linConverging? (or (not quadConverging?) (< tss tvv)))
                (label FixedShift-LinFirst)
                (tryLin ss #f quadConvergingLimit linConvergingLimit)]
               [else
                (label FixedShift-QuadFirst)
                (tryQuad K uu vv #f quadConvergingLimit linConvergingLimit)])]
            [else
             (label FixedShift-nonconvergingpass)
             (loop (+ j 1) K vv ss tv ts quadConvergingLimit linConvergingLimit)])])])))
(TEST
 ;passing pass0-or-factor QuadFirst QuadConverged
 (check-within (FixedShift 5 #(1. 2. 3. 4. 5.) #(1. 2. 3. 4.) 1.0 2.0)
               '(#(1.0 2.575630959115296 2.394455557338827)
                 (0.28781547955764797+1.4160930801719078i 0.28781547955764797-1.4160930801719078i))
               epsilon100)
 ;passing pass0-or-factor LinFirst LinConverged
 (check-within (FixedShift 5 #(1. 2. 3. 4. -5.) #(1. 2. 3. 4.) 1.0 2.0)
               '(#(1.0 2.68412431945307 4.836274723373266 7.308613153815818)
                 (0.6841243194530697))
               epsilon100)
 ;passing pass0-or-factor nonconvergingpass QuadFirst QuadConverged
 (check-within (FixedShift 5 #(5.973052788152122 3.1198874346298604 4.732251119406017 3.6024342708537196 4.181120877543731)
                           #(5.973052788152122 -7.411175697861289 -0.024070219044631358 -0.4006197810018648)
                           3.4548598408258635 0.586936423108628)
               '(#(5.973052788152122 -4.285169564149636 5.5226517874526735)
                 (-0.6198720538237862+0.6106098345570848i -0.6198720538237862-0.6106098345570848i))
               epsilon100)
 ;passing pass0-or-factor LinFirst LinOver LinFirst QuadSecondNorm QuadConverged
 (check-within (FixedShift 5 #(8.41755012535733 4.671578854715546 0.5931615068990723 0.7322427309831809 5.728464948833154)
                           #(8.401638613441222 9.708937329579836 0.33872763171218045 0.1468471881337965)
                           0.24442525134432416 9.30559289538379)
               '(#(8.41755012535733 13.252560535681688 8.27797623788355)
                 (0.5097077863021263+0.6574273375997998i 0.5097077863021263-0.6574273375997998i))
               epsilon100)
 ;passing pass0-or-factor LinFirst LinOver nonconvergingpass QuadFirst QuadOver nonconvergingpass maxiter
 (check-equal? (FixedShift 5 #(6.7460988725508955 5.98370659970934 6.157731644531755 4.907674864119937 3.8729258686230943)
                           #(8.877633271400752 0.038665127484674225 5.24238410415498 4.852226488120647)
                           1.2246379011135278 9.917716291473479)
               'maxiter)
 ;passing ... linSecond ...
 (check-within (FixedShift 11 #(61.52697196174651 36.82318279967228 -47.989940452833565)
                           #(-14.281125965172919 -30.810404431206194)
                           62.62559015912069 72.73878188097541)
               '(#(61.52697196174651 75.78460263823895)
                 (0.6332413020876496))
               epsilon100)
 ;passing ... QuadSecondSpec
 (check-within (FixedShift 18 #(-74.46775787726362 90.3506061511408 -41.6749987910501 -12.605712335088313 -3.9257546925351363 -66.56163578033919 -36.151837492264384)
                           #(55.20898627198051 41.74299097679142 23.90535938840239 19.045011969600466 -21.305286565679026 1.629283218386334)
                           26.907593802730446 1.2786560845469381)
               '(#(-74.46775787726362 172.36524977999846 -206.62332203773178 157.35777413703312 -108.18276080133784)
                 (-0.5506721698539164+0.17588035331998092i -0.5506721698539164-0.17588035331998092i))
               epsilon100)
  
  #;(let ();for searching branches
    (define (rdm)(- (* 200 (random)) 100))
    (for ([i (in-range 10000)])
      (define p (for/vector ([i (in-range (+ (random 20) 3))])(rdm)))
      (define NN (vector-length p))
      (define K (for/vector ([i (in-range NN)])(rdm)))
      (define L2 (+ (random 20) 5))
      (define sr (rdm))
      (define bnd (rdm))
      (println (list i 'FixedShift L2 sr bnd K (- NN 1) p NN))
      (FixedShift L2 sr bnd K (- NN 1) p NN)))
  )

(define (evalPoly P x)
  (for/fold ([ff (rf P 0)])
            ([ai (in-vector P 1)])
       (+ (* ff x)ai)))
(define (evalPoly+df P x)
  (define degree (- (vector-length P) 1))
  (prepare (f* *)(df* *))
  (s! df* (rf P 0))(s! f* (rf P 0))
  (for ([i (in-range 1 degree)])
    (s! f* (+ (* x (rf f*)) (rf P i)))
    (s! df* (+ (* x (rf df*)) (rf f*))))
  (s! f* (+ (* x (rf f*)) (rf P degree)))
  (values (rf f*)(rf df*)))

; Scale if there are large or very small coefficients
; Computes a scale factor to multiply the coefficients of the polynomial.
; The scaling is done to avoid overflow and to avoid undetected underflow 
; interfering with the convergence criterion.
; The factor is a power of the base. (hardcoded to 2)
(define (scalePoly P)
  (define-values (a-min a-max)
    (for/fold ([a- +inf.0][a+ -inf.0])
              ([ai (in-vector P)])
      (define Ai (abs ai))
      (values (min a- Ai)(max a+ Ai))))
  (define sc (fl/ (fl/ +FLT_MIN epsilon.0) a-min));was using +min.0, but that is for double, not single Float
  (define s
    (cond
      [(or (and (< sc 1) (<= 10 a-max))
           (and (< 1 sc) (<= a-max (/ +FLT_MAX sc))))
       (label scaleP-scalable)
       (define l (floor (fl+ (fl/ (fllog (if (= sc 0) +FLT_MIN sc))
                                  (fllog 2.0))
                             0.5)))
       (flexpt 2.0 l)]
      [else (label scaleP-unscalable) 1.0]))
  (cond
    [(= s 1.0) (label scaleP-not-scaled) P]
    [else
     (label scaleP-scaled)
     (for/vector ([ai (in-vector P)])
       (* ai s))]))
(TEST
  (let ()
    (define p* (vector 1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
    (check-within (scalePoly #(1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
                  #(5.293955920339377e-23 -2.649995515044282e-22 5.306029962073926e-22 -5.3120727149296205e-22 2.6590596436449997e-22 -5.324169677789603e-23) epsilon100)))

;Compute lower bound on moduli of zeros
(define (lowerBoundZeroPoly P)
  (define N (- (vector-length P) 1))
  (define pt (for/vector ([ai (in-vector P)])(abs ai)))
  (define pt_n (- (abs (rf P N))))
  (s! pt N pt_n)
  ;Compute upper estimate of bound
  (define x (exp (/ (- (log (- pt_n)) (log (rf pt 0))) N)))
  (when (not (= 0.0 (rf pt (- N 1))));If Newton step at the origin is better, use it
    (label LBZP-newtonstep)
    (define xm (- (/ pt_n (rf pt (- N 1)))))
    (when (< xm x)(set! x xm)))
  ;Chop the interval (0, x) until f<=0
  (define xm x)
  (for ([_ (in-naturals)]
        #:break (< (evalPoly pt xm) 0))
    (set! x xm)(set! xm (* 0.1 x)))
  ;Do Newton iteration until x converges to two decimal places
  (let loop ([x x])
    (define-values (f df)(evalPoly+df pt x))
    (define dx (/ f df))
    (define x+ (- x dx))
    (cond
      [(<= (abs dx) (* (abs x+) .005))(label LBZP-converged) x+]
      [else (label LBZP-loop)(loop x+)])))

(define (roots2 P)
  (match P
    [(vector a b)(list (- (/ b a)))]
    [(vector a b c)
     (for/list ([z (in-list (Quad a b c))])
       (+ (car z) (* +i (cdr z))))]))

(define (ZeroShift maxiter P K1)
  (define N (vector-length K1))
  (define K* (vector-copy K1))
  (define NM1 (- N 1))
  (define aa (rf P N))
  (define bb (rf P NM1))
  (define zerok (= 0.0 (rf K* NM1)))
  (for/fold ([zerok (= 0.0 (rf K* NM1))])
            ([iter (in-range maxiter)])
    (cond
      [zerok ;Use unscaled form of recurrence
       (label ZeroShift-unscaled)
       (for ([i (in-range NM1)])(s! K* (- NM1 i) (rf K* (- NM1 i 1))))
       (s! K* 0 0)
       (= 0.0 (rf K* NM1))]
      [else ;Use scaled form of recurrence if value of K at 0 is nonzero
       (label ZeroShift-scaled)
       (define t (- (/ aa (rf K* NM1))))
       (for ([i (in-range NM1)])
         (define j (- NM1 i))
         (s! K* j (+ (* t (rf K* (- j 1))) (rf P j))))
       (s! K* 0 (rf P 0))
       (<= (abs (rf K* NM1)) (* (abs bb) epsilon10))]))
  K*)

(define rotator (make-polar 1 (* 94 RADFAC)))
(define (1root iteration-scheme0 P angle)
  (define N (- (vector-length P) 1))
  (define iteration-scheme (if (vector? iteration-scheme0) (vector-copy iteration-scheme0) (make-vector 6 iteration-scheme0)))
  ;Find the largest and smallest moduli of the coefficients
  (define P+ (scalePoly P))
  ;Compute lower bound on moduli of zeros
  (define bnd (lowerBoundZeroPoly P))
  ;Compute the (scaled) derivative as the initial K polynomial => K = p'/N
  (define K_0 (for/vector ([i (in-range N)]
                           [ai (in-vector P+)])
                (if (= i 0) ai (/ (* (- N i) ai) N))))
  ;do 5 steps with no shift
  (define K_1 (ZeroShift (rf iteration-scheme 0) P+ K_0))
  ;Loop to select the quadratic corresponding to each new shift
  (let loop ([j 0][angle angle])
    (cond
      [(< j (rf iteration-scheme 1))
       ;Quadratic corresponds to a double shift to a non-real point and its
       ;complex conjugate. The point has modulus BND and angle rotated
       ;by 94° from the previous shift
       (define angle+ (* angle rotator))
       (define sr (* bnd (real-part angle+)))
       ;The second stage jumps directly to one of the third stage iterations and returns here.
       (s! iteration-scheme 3 (* (+ j 1) (rf iteration-scheme 2)))
       (match (FixedShift iteration-scheme P+ K_1 sr bnd)
         ;successful, return the deflated polynomial and zero(s)
         [(list qp roots) (label 1root-rootfound) (list qp angle+ roots)]
         ;If the iteration is unseccessful, another quadratic is chosen after restoring K
         [else (label 1root-nexttry)(loop (+ j 1) angle+)])]
      [else (label 1root-maxiter) #f])))

(define (roots P [iteration-scheme #(5 20 20 0 20 10)])
  (define degree (- (vector-length P) 1))
  (cond
    [(< degree 1) (label roots-degree1)'degree<1]
    ;Do a quick check to see if leading coefficient is 0
    ;The leading coefficient is zero. No further action is taken. Program terminated
    [(= 0.0 (rf P 0)) (label roots-leadingzero) 'leading-zero]
    [else
     ;Remove zeros at the origin, if any
     (define s@0 (for/sum ([i (in-range degree -1 -1)] #:break (not (= 0 (rf P i))))(label roots-s@0)1))
     (define N (- degree s@0))
        
     ;Main loop
     (let loop ([P (vector-copy P 0 (+ N 1))]
                [angle (make-polar 1 (* -45 RADFAC))]
                [ans (for/list ([i (in-range s@0)]) 0.0)])
       (cond
         [(<= (vector-length P) 1) (label roots-onlyZeroes) ans]
         [(<= (vector-length P) 3)
          (label roots-roots2)
          (append ans (roots2 P))]
         [else
          (match (1root iteration-scheme P angle)
            [(list qP angle+ ans+)
             (loop qP angle+ (append ans ans+))]
            [#f
             (label roots-maxiter)
             'no-fixed-shift-convergence])]))]))
(module+ test ;TEST
  ;'roots-s@0'roots-roots2'Quad-3.1.2.2'Quad-3.2.2.1.1'Quad-3.2.2.2.2
  (check-within (roots #(1 2 1 0 0)) '(0 0 -1 -1) epsilon.0)

  ;'scaleP-unscalable'scaleP-not-scaled'LBZP-newtonstep'LBZP-loop'LBZP-converged'ZeroShift-scaled'QuadraticSyntheticDivision'calcSC-type2'nextK-normal'newest-type1'newest-normal'FixedShift-pass0-or-factor'FixedShift-QuadFirst'Quad-3.1.1'Quad-3.1.1.2'Quad-3.2.1'QuadIT-norelstp'calcSC-type1'QuadIT-normal'newest-type2'QuadIT-converged'FixedShift-QuadConverged'1root-rootfound 
  (check-within (roots #(1. 1. 1. 1. 1.))
                '(0.3090169943749474+0.9510565162951535i
                  0.3090169943749474-0.9510565162951535i
                  -0.8090169943749475+0.5877852522924729i
                  -0.8090169943749475-0.5877852522924729i)
                epsilon.0)
  (check-within (roots #(1. 2. 3. 4. 5.))
                '(0.287815479557648+1.4160930801719078i 0.287815479557648-1.4160930801719078i -1.287815479557648+0.8578967583284905i -1.287815479557648-0.8578967583284905i)
                epsilon100)

  ;'FixedShift-LinFirst'RealIT-scaled'RealIT-converged'FixedShift-LinConverged'FixedShift-nonconvergingpass
  (check-within (roots #(1. 2. 3. 4. -5.))
                '(0.6841243194530697 -2.0591424445683537 -0.3124909374423581+1.8578744391719895i -0.3124909374423581-1.8578744391719895i)
                epsilon100)
  (check-within (roots #(1. 3. 1. 0.08866210790363471))
                '(-0.18350341911302884 -0.1835034190315191 -2.632993161855452)
                epsilon100)

  ;'scaleP-scalable'scaleP-scaled'Quad-3.2.2.1.2
  ;irritatingly difficult (flpoly-from-roots .9998 .9999 1. 1.003 1.003)
  (check-within (roots #(1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
                '(0.9998971273942638 1.0029951281002996 0.9995771489617781 1.0030048540302405 1.0002257415134181)
                epsilon100)
  ;same but exact
  ;(mfr #(1 -50057/10000 501140361/50000000 -501711082871/50000000000 251141082742009/50000000000000 -50285360871009/50000000000000))

  ;'newest-temp0'RealIT-maxiter'FixedShift-LinOver'FixedShift-maxiter'1root-nexttry'QuadIT-go-linear'FixedShift-QuadOver
  (check-within (roots #(1e-8 1e-16 1e-20 -1e25 38.5))
                '(3.85e-24 100000000000.0 -50000000000.0+86602540378.44386i -50000000000.0-86602540378.44386i)
                epsilon100)

  ;'Quad-3.1.1.1
  (check-within (roots #(1 -1.1262458658846637 -1.0101179104905715 0.1369529023140107  -0.07030543743385387  0.34354611896594955  0.7685557744974647  0.9049868924344322 -0.4694264319569345))
                '(0.37998534697611247 -0.6385228013511156+0.6232370795625065i -0.6385228013511156-0.6232370795625065i 0.16462177207475362+0.9168019517176714i 0.16462177207475362-0.9168019517176714i 1.1475571613888245 -1.00470119265642 1.5512066087288707)
                epsilon100)

  ;'QuadIT-nonconverging'FixedShift-LinSecond
  (check-within (roots #(91.18809308091258 10.754641992264794 -69.33386824593055 75.32381621826295 -99.6568435171208 -8.055652043683352) #(16 7 6 13 6 6))
                '(-0.0761433179981868 0.18998072135406274+0.8836475713376982i 0.18998072135406274-0.8836475713376982i 0.9993550538048728+0.0i -1.4211122825020175+0.0i)
                epsilon100)
  ;'FixedShift-QuadSecondNorm
  (check-within (roots #(89.66884488498786 -5.035976424692905 -27.674824222075614 -96.72180780166202 -76.0750414392931 74.2881927760188 -18.803978038771874 -88.40539985995814) #(10 12 9 8 20 5))
                '(0.5869751784061364+0.5817789453984389i 0.5869751784061364-0.5817789453984389i -0.8415758009696521+0.238152739346124i -0.8415758009696521-0.238152739346124i -0.3656188900542874+1.1496345853579042i -0.3656188900542874-1.1496345853579042i 1.296600966778984)
                epsilon100)
  ;'RealIT-zero-cluster'FixedShift-QuadSecondSpec
  (check-within (roots #(-40.64181224757269 -32.38161144204791 40.40535730410238 -65.15400236286979 -62.242148105606155 50.1741360957316 35.03883110547369 72.04602337106431 -60.304657589497225) #(6 15 17 13 13 11))
                '(0.7268085894914331+0.057272261653429815i 0.7268085894914331-0.057272261653429815i -0.3924569734187341+0.799423579895323i -0.3924569734187341-0.799423579895323i -1.4278711153456562+0.20522664007256347i -1.4278711153456562-0.20522664007256347i 0.6951414539634508+1.0992008490881526i 0.6951414539634508-1.0992008490881526i)
                epsilon100)
  ;'QuadIT-relstp'QuadIT-maxiter
  (check-within (roots #(49.710497758300875 83.86411816900053 -36.84017911151918 -14.016998958665823 17.093717575886586 -58.21731735700788 -55.75463399220348 -1.192533142875618) #(10 7 13 11 10 7))
                '(-0.02189268218917173 -0.740897582574855+0.3020074801637734i -0.740897582574855-0.3020074801637734i 0.34616045877917445+0.8686851231541562i 0.34616045877917445-0.8686851231541562i 1.028202297696444 -1.9038858291033882)
                epsilon100)
  ;'1root-maxiter'roots-maxiter
  (check-within (roots #(22.709304169643517 -87.36732242917714 13.288056236672148 -41.39643819314873 75.18712911729767 -35.487285112346356 -93.38667030083654 -18.78550828140827 39.560341795103426 72.3237416807884 56.78347959438429 58.343051452039475 -31.924565751177653 67.97234288841659 13.739862585880672 57.482326672487886 2.103801825454184 -96.50241534051075 17.05682765408889) #(18 5 6 17 8 16))
                'no-fixed-shift-convergence
                epsilon100)
  ;'roots-leadingzero
  (check-within (roots #(0 -34.31069728932926 -86.06077988367579 -29.809362734748845 -32.30243846748657 -46.697569318370526 93.20029574485068 8.046955603586227) #(19 16 11 17 15 7))
                'leading-zero
                epsilon100)
  ;'ZeroShift-unscaled
  (check-within (roots #(-17.756065857424794 25.893174382341186 -60.51441252673925 0 67.74493116488347) #(8 19 8 9 17 6))
                '(1.1219852897128721 -0.8443057836142638 0.5902962670087036+1.9181033950461768i 0.5902962670087036-1.9181033950461768i)
                epsilon100)
  ;'roots-onlyZeroes
  (check-within (roots #(-188.89404654362278 0 0) #(16 17 7 5 9 7))
                '(0.0 0.0)
                epsilon100)
  ;'roots-degree1
  (check-within (roots #(-188.89404654362278) #(16 17 7 5 9 7))
                'degree<1
                epsilon100)


  #;(let ();for searching branches
    (define (rdm)(let ([k (random 1000000000)])(- (* 2 k (random)) k)))
    (for ([i (in-range 1000000000)])
      (define p (for/vector ([i (in-range (+ (random 17) 3))])(rdm)))
      (define r (for/vector ([i (in-range 6)]) (+ 5 (random 16))))
      (define out (open-output-string))
      (define ans
        (parameterize ([current-output-port out])
          (roots p r)))
      (define S (get-output-string out))
      (unless (equal? "" S)
        (displayln i)
        (displayln S)
        (displayln (list 'check-within (list 'roots p r)
                         ans
                         'epsilon100))))))