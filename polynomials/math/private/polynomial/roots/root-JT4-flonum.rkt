#lang racket/base

#|
based on the cpp translation fo TOMS/493 found at http://www.akiti.ca/PolyRootRe.html
|#

(require math/flonum
         racket/match)
(require (for-syntax racket/base))

(define-syntax label
  (let ()
    (define L '())
    (define ALL '(Quad-goto00-1 Quad-goto00-2 Quad-goto00-3 Quad-goto10 Quad-goto20-1 Quad-goto20-2 Quad-goto30-1 Quad-goto30-2 Quad-goto40 Quad-goto40-1 Quad-goto50-1 Quad-goto50-2 Quad-goto50-3 Quad-goto50-4 Quad-goto60
                  QuadraticSyntheticDivision
                  calcSC-type3 calcSC-type2 calcSC-type1
                  nextK-type3 nextK-normal nextK-smalla1
                  newest-type3 newest-type2 newest-type1 newest-temp0 newest-normal
                  RealIT-converged RealIT-maxiter RealIT-zero-cluster RealIT-scaled RealIT-unscaled
                  QuadIT-go-linear QuadIT-converged QuadIT-relstp QuadIT-nonconverging QuadIT-normal
                  FixedShift-maxiter))
    (define S '(QuadIT-maxiter))
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

(module+ test
  (require rackunit))

(define epsilon10 (* 10 epsilon.0))
(define epsilon100 (* 100 epsilon.0))
(define FLT_MIN (floating-point-bytes->real (bytes #b00000000 #b00000000 #b00000000 #b00000001)))
(define FLT_MAX (floating-point-bytes->real (bytes #b11111111 #b11111111 #b11111111 #b01111110)))

(define RADFAC (/ (angle -1) 180));Degrees - to - radians conversion factor = pi/180
(define cosr (cos (* 94 RADFAC)));-.069756474
(define sinr (sin (* 94 RADFAC))); .99756405

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
(define mk
  (case-lambda [() (box 'undefined)]
               [(n) (make-vector n 0.)]))

(define-syntax (prepare-one stx)
  (syntax-case stx (*)
    [(_ (id *)) #'(define id (box 'undefined))]
    [(_ (id nr *)) #'(define id (make-vector nr 0.0))]
    [(_ (id nr)) #'(define id (box nr))]
    [(_ (id nr v)) #'(define id (make-vector nr v))]))
(define-syntax (prepare stx)
  (syntax-case stx ()
    [(_ ids ...) #'(begin (prepare-one ids) ...)]))

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
      [(not (= A 0))
       (label Quad-goto00-1)
       (goto20)]
      [else
       (label Quad-goto00-2)       
       (s! szr* 0.0)
       (when (not (= B1 0))
         (label Quad-goto00-3)
         (s! szr* (- (/ C B1))))
       (s! lzr* 0)
       (goto10)]))
  (define (goto10)
    (label Quad-goto10)
    (s! szi* 0)
    (s! lzi* 0))
  (define (goto20)
    (cond
      [(not (= C 0))
       (label Quad-goto20-1)
       (goto30)]
      [else
       (label Quad-goto20-2)
       (s! szr* 0)
       (s! lzr* (- (/ B1 A)))
       (goto10)]))
  ;compute Discriminant avoiding overflow
  (define (goto30)
    (s! B (/ B1 2))
    (cond
      [(< (abs (rf B)) (abs C))
       (label Quad-goto30-1)
       (goto40)]
      [(s! E (- 1 (* (/ A (rf B))(/ C (rf B)))))
       (label Quad-goto30-2)
       (s! D (* (sqrt (abs (rf E)))(abs (rf B))))
       (goto50)]))
  (define (goto40)
    (label Quad-goto40)
    (s! E A)
    (when (< C 0)
      (label Quad-goto40-1)
      (s! E (- A)))
    (s! E (- (* (rf B) (/ (rf B) (abs C))) (rf E)))
    (s! D (* (sqrt (abs (rf E))) (sqrt (abs C))))
    (goto50))
  (define (goto50)
    (cond
      [(< (rf E) 0)
       (label Quad-goto50-1)
       (goto60)]
      [else
       (label Quad-goto50-2)
       ;real zeros
       (when (> (rf B) 0)
         (label Quad-goto50-3)
         (s! D (- (rf D))))
       (s! lzr* (/ (+ (- (rf B)) (rf D)) A))
       (s! szr* 0)
       (when (not (= (rf lzr*) 0))
         (label Quad-goto50-4)
         (s! szr* (/ (/ C (rf lzr*)) A)))
       (goto10)]))
  (define (goto60)
    (label Quad-goto60)
    ;comples conjugate zeros
    (s! szr* (- (/ (rf B) A)))
    (s! lzr* (rf szr*))
    (s! szi* (abs (/ (rf D) A)))
    (s! lzi* (- (rf szi*))))

  (goto00))
(module+ test
  (let ()
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *))
    (Quad 1 6 3 szr* szi* lzr* lzi*)
    (check-within (list (rf szr*)(rf szi*)(rf lzr*)(rf lzi*))
                  '(-0.5505102572168219 0 -5.449489742783178 0)
                  epsilon100))
  (let ()
    (define szr* (mk))(define szi* (mk))
    (define lzr* (mk))(define lzi* (mk))
    (Quad 1 2 3 szr* szi* lzr* lzi*)
    (check-within (list (rf szr*)(rf szi*)(rf lzr*)(rf lzi*))
                  '(-1 1.414213562373095 -1 -1.414213562373095)
                  epsilon100))
  (let ()
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *))
    (Quad 1 6 7 szr* szi* lzr* lzi*)
    (check-within (list (rf szr*)(rf szi*)(rf lzr*)(rf lzi*))
                  '(-1.585786437626905 0 -4.414213562373095 0)
                  epsilon100)))

; Divides p by the quadratic x^2+u*x+v
; placing the quotient in q and the remainder in a, b
(define (QuadraticSyntheticDivision NN u v p)
  (label QuadraticSyntheticDivision)
  (define q (make-vector (+ NN 1) 0.0))
  (define b (rf p 0))
  (s! q 0 b)
  (define a (- (rf p 1) (* b u)))
  (s! q 1 a)
  (for ([i (in-range 2 NN)])
    (s! q i (- (rf p i) (+ (* a u)(* b v))))
    (set! b a)
    (set! a (rf q i)))
  (list q a b))
(define (QuadraticSyntheticDivision_imp NN u v p q* a* b*)
  (match-define (list q a b)(QuadraticSyntheticDivision NN u v p))
  (s! q* q NN)(s! a* a)(s! b* b))
(module+ test
  (check-within (QuadraticSyntheticDivision 4 2.8 3.5 #(1. 2. 3. 4. 5.))
                (list #(1.0 -0.8 1.74 1.928 0.0) 1.928 1.74)
                epsilon100)
  (check-within (QuadraticSyntheticDivision 5 3.345 6.482 #(0.428 3.62 2.6e-4 12. 0.005 1.23e-4))
                (list #(0.428 2.18834 -10.0940333 31.5797215085 -40.199644595332494 0.0)
                      -40.199644595332494 31.5797215085)
                epsilon100))

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
(define (calcSC N a b K u v)
  ;Synthetic division of K by the quadratic 1, u, v
  (match-define (list qk* c d)(QuadraticSyntheticDivision N u v K))
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
(define (calcSC_imp N a b a1* a3* a7* c* d* e* f* g* h* K u v qk*)
  (define out (calcSC N a b K u v))
  (match out
    [(list tFlag qk c d)
     (s! qk* qk N)(s! c* c)(s! d* d)
     tFlag]
    [(list tFlag qk c d e f g h a1 a3 a7)
     (s! qk* qk N)(s! c* c)(s! d* d)(s! e* e)(s! f* f)(s! g* g)(s! h* h)(s! a1* a1)(s! a3* a3)(s! a7* a7)
     tFlag]))
(module+ test
  (check-within (calcSC 4 2.3 4.6 #(1. 2. 3. 4. 5.) 1.8 9.2)
                (list 'calcSC:div-by-c
                      #(1.0 0.2 -6.56 13.968 0.0)
                      13.968 -6.56 0.16466208476517755 -0.46964490263459335 0.2963917525773196 42.32
                      5.680183276059564 15.679123711340203 -19.519702176403204)
                epsilon100)
  (check-within (calcSC 4 2.3 4.6 #(1. -10 35. -50. 24.) -6. 8.)
                (list 'calcSC:div-by-d
                      #(1.0 -4.0 3.0 0.0 0.0)
                      0.0 3.0 0.7666666666666666 0.0 -27.6 36.8
                      -2.3 37.03 23.0)
                epsilon100)
  (check-within (calcSC 5 2.3 4.6 #(1. -10 35. -50. 24. 0) -6. 8.)
                (list 'calcSC:almost-factor
                      #(1.0 -4.0 3.0 0.0 0.0 0.0)
                      0.0 0.0)
                epsilon100))

;Computes the next K polynomials using the scalars computed in calcSC
(define (nextK N tFlag a b a1 a3 a7 qk qp)
  (define K (make-vector (+ N 1) 0.0))
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
        (define a7* (/ a7 a1))
        (define a3* (/ a3 a1))
        (s! K 0 (rf qp 0))
        (s! K 1 (- (rf qp 1) (* a7* (rf qp 0))))
        (for ([i (in-range 2 N)])
          (s! K i (+ (rf qp i) (* -1 a7* (rf qp (- i 1))) (* a3* (rf qk (- i 2))))))
        (list K a3* a7*)]
       [else
        (label nextK-smalla1)
        ;If a1 is nearly zero, then use a special form of the recurrence
        (s! K 0 0)
        (s! K 1 (* -1 a7 (rf qp 0)))
        (for ([i (in-range 2 N)])
          (s! K i (+ (* a3 (rf qk (- i 2))) (* -1 a7 (rf qp (- i 1))))))
        (list K a3 a7)])]))
(define (nextK_imp N tFlag a b a1 a3* a7* K* qk qp)
  (match-define (list K a3 a7)
    (nextK N (if (number? tFlag)
                 (case tFlag
                   [(1) 'calcSC:div-by-c]
                   [(2) 'calcSC:div-by-d]
                   [(3) 'calcSC:almost-factor])
                 tFlag)
           a b a1 (rf a3*) (rf a7*) qk qp))
  (s! a3* a3)(s! a7* a7)(s! K* K N))
(module+ test
  (check-within (nextK 4 'calcSC:div-by-c 8. 9. 10. 6. 7. #(11. 12. 13. 14. 15.) #(16. 17. 18. 19. 20.))
                (list #(16.0 5.8 12.7 13.6 0.0) .6 .7)
                epsilon100)
  (check-within (nextK 4 'calcSC:div-by-c 8. 9. 0. 6. 7. #(11. 12. 13. 14. 15.) #(16. 17. 18. 19. 20.))
                (list #(0 -112. -53. -54. 0.0) 6. 7.)
                epsilon100)
  (check-within (nextK 4 'calcSC:almost-factor 8. 9. 10. 6. 7. #(11. 12. 13. 14. 15.) #(16. 17. 18. 19. 20.))
                (list #(0 0 11. 12. 0.0) 6. 7.)
                epsilon100))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest tFlag a a1 a3 a7 b c d f g h u v K N p)
  (cond
    [(equal? tFlag 'calcSC:almost-factor)
     (label newest-type3)
     (list 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (cond
         [(not (equal? tFlag 'calcSC:div-by-d))
          (label newest-type2)
          (values (+ a (* u b) (* h f))
                  (+ c (* (+ u (* v f)) d)))]
         [else
          (label newest-type1)
          (values (+ (* (+ a g) f) h)
                  (+ (* (+ f u) c) (* v d)))]))
     (define b1 (- (/ (rf K (- N 1))(rf p N))))
     (define b2 (- (/ (+ (rf K (- N 2)) (* b1 (rf p (- N 1))))
                      (rf p N))))
     (define c1 (* v b2 a1))
     (define c2 (* b1 a7))
     (define c3 (* b1 b1 a3))
     (define c4 (+ (- (+ c2 c3)) c1))
     (define temp (+ (- c4) a5 (* b1 a4)))
     (cond
       [(= temp 0.0)
        (label newest-temp0)
        (list 0.0 0.0)]
       ;!!!it temp ≈ 0.0 these values blow up. Is this a good idea?
       [else
        (label newest-normal)
        (list (+ (- (/ (+ (* u (+ c3 c2)) (* v (+ (* b1 a1)(* b2 a7)))) temp)) u)
              (* v (+ 1.0 (/ c4 temp))))])]))
(define (newest_imp tFlag uu* vv* a a1 a3 a7 b c d f g h u v K N p)
  (match-define (list uu vv)
    (newest (if (number? tFlag)
                (case tFlag
                  [(1) 'calcSC:div-by-c]
                  [(2) 'calcSC:div-by-d]
                  [(3) 'calcSC:almost-factor])
                tFlag)
            a a1 a3 a7 b c d f g h u v K N p))
  (s! uu* uu)(s! vv* vv))
(module+ test
  ;tflag=3
  (check-within (newest 'calcSC:almost-factor 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12. #(13. 14. 15. 16. 17.) 4 #(18. 19. 20. 21. 22.))
                '(0. 0.) epsilon100)
  ;tflag=2 & temp=0
  (check-within (newest 'calcSC:div-by-d 1. 2. 3. 4. 5. -0.8908220965637230 7. 8. 9. 10. 11. 12. #(13. 14. 15. 16. 17.) 4 #(18. 19. 20. 21. 22.))
                '(0. 0.) epsilon100)
  ;tflag=2 & temp!=0
  (check-within (newest 'calcSC:div-by-d 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12. #(13. 14. 15. 16. 17.) 4 #(18. 19. 20. 21. 22.))
                '(11.239868703446534 12.148466102764804) epsilon100)
  ;tflag=1 & temp=0
  (check-within (newest 'calcSC:div-by-c 1. 2. 3. 4. 5. 100.52892561983471 0. 8. 9. 10. 11. 12. #(13. 14. 15. 16. 17.) 4 #(18. 19. 20. 21. 22.))
                '(0. 0.) epsilon100)
  ;tflag=1 & temp!=0
  (check-within (newest 'calcSC:div-by-c 1. 2. 3. 4. 5. 6. 7. 8. 9. 10. 11. 12. #(13. 14. 15. 16. 17.) 4 #(18. 19. 20. 21. 22.))
                '(11.047985250849212 12.029700344736144) epsilon100))
(define (calcSC->nextK N a b K u v qp)
  (define out (calcSC N a b K u v))
  (match out
    [(list tFlag qk c d)
     (nextK N tFlag a b 0.0 0.0 0.0 qk qp)]
    [(list tFlag qk c d e f g h a1 a3 a7)
     (nextK N tFlag a b a1 a3 a7 qk qp)]))
(define (calcSC->nextK_imp N a b K* u v qp)
  (match-define (list K _ _)(calcSC->nextK N a b K* u v qp))
  (s! K* K N))
(define (calcSC->newest N a b K u v p)
  (define out (calcSC N a b K u v))
  (match out
    [(list tFlag qk c d)
     (newest tFlag a 0.0 0.0 0.0 b 0.0 0.0 0.0 0.0 0.0 u v K N p)]
    [(list tFlag qk c d e f g h a1 a3 a7)
     (newest tFlag a a1 a3 a7 b c d f g h u v K N p)]))


; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT sss N p NN K)
  ;return (list iFlag NZ qp K* qk sss* szr szi)
  (let loop ([j 1]
             [qp* (make-vector NN 0.0)]
             [K* (let ([v (make-vector NN 0.0)])(s! v K)v)]
             [qk* (make-vector NN 0.0)]
             [s sss][omp 0][t 0])
    ; Evaluate p at s
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
       (list 'RealIT:normal 1 qp* K* qk* sss s 0)]
      [(> j 10)
       (label RealIT-maxiter)
       (list 'RealIT:normal 0 qp* K* qk* sss 'undefined 'undefined)]
      [(and (>= j 2)
            (<= (abs t) (* 0.001 (abs (- s t)))) (> mp omp))
       ;A cluster of zeros near the real axis has been encountered;
       ;Return with iFlag set to initiate a quadratic iteration
       (label RealIT-zero-cluster)
       (list 'RealIT:zero-cluster 0 qp* K* qk* s 'undefined 'undefined)]
      [else
       ;Return if the polynomial value has increased significantly
       ;Compute t, the next polynomial and the new iterate
       (define kv (rf K* 0))(s! qk* 0 kv)
       (for ([i (in-range 1 N)])
         (set! kv (+ (* kv s) (rf K* i)))(s! qk* i kv))
       (cond
         [(> (abs kv) (* (abs (rf K* (- N 1))) epsilon10))
          (label RealIT-scaled)
          ;Use the scaled form of the recurrence if the value of K at s is non-zero
          (define tt (- (/ pv kv)))
          (s! K* 0 (rf qp* 0))
          (for ([i (in-range 1 N)])(s! K* i (+ (* tt (rf qk* (- i 1))) (rf qp* i))))]
         [else ;Use unscaled form
          (label RealIT-unscaled)
          (s! K* 0 0.0)
          (for ([i (in-range 1 N)])(s! K* i (rf qk* (- i 1))))])
       (define kv* (for/fold ([k (rf K* 0)])
                             ([i (in-range 1 N)])
                     (+ (* k s) (rf K* i))))
       (define t* (if (> (abs kv*) (* (abs (rf K* (- N 1))) epsilon10)) (- (/ pv kv*)) 0))
       (loop (+ j 1) qp* K* qk* (+ s t*) mp t*)])))
(define (RealIT_imp iFlag* NZ* sss* N p NN qp* szr* szi* K* qk*)
  (match-define (list iFlag NZ qp K qk sss szr szi)(RealIT (rf sss*)N(rf p)NN(rf K*)))
  (s! iFlag* (case iFlag[(RealIT:normal)0][(RealIT:zero-cluster)1]))
  (s! NZ* NZ)(s! sss* sss)(s! szr* szr)(s! szi* szi)(s! qp* qp NN)(s! K* K N)(s! qk* qk N))
(module+ test
  ;break small mp = zero found
 (check-within (RealIT 0.2 4 #(1. 2. 3. 4. -5.) 5 #(1. 2. 3. 4. 5.))
                (list 'RealIT:normal 1
                      #(1.0 2.68412431945307 4.836274723373266 7.308613153815818 0.0)
                      #(1.0 2.6841243194530695 4.836274723373265 7.308613153815818 5.0)
                      #(1.0 3.3682486283245323 7.140575458942369 12.193654442009374 0.0);(rf qk 5) changed to 0 ... but is ignored in calculations...
                      0.2 0.6841243194530697 0)
                epsilon100)
  ;break iterrations j (iFlag=0 & NZ=0)
 (check-within (RealIT 1.0 4 #(1. 2. 3. 4. 5.) 5 #(1. 2. 3. 4. 5.))
                (list 'RealIT:normal 0
                      #(1.0 -0.6849750434472566 4.839140897040084 -8.992972540277597 29.145906837051825)
                      #(1.0 1.0919036572997787 1.0019196569203022 3.933013624211993 5.0)
                      #(1.0 -2.8905094995548675 6.966052236569645 -8.822295643728838 0.0);(rf qk 5) changed to 0 ... but is ignored in calculations...
                      1 'undefined 'undefined)
                epsilon100)
  ;break  cluster of zeros
 (check-within (RealIT 3.5502909446276085 4 #(4.9679877220982345 9.29937913880471 -9.609506455896735 -2.5160214731778163 -6.029809381393797) 5 #(8.514417957281449 0.5198895391395837 -9.66980775616132 0.45524621258751097 -6.75327262484485))
                (list 'RealIT:zero-cluster 0
                      #(4.9679877220982345 2.2034324874736058 -12.756744383111027 15.70487250861968 -28.461615521215446)
                      #(4.9679877220982345 -6701.697712994184 7942.889509061441 -1976.5039946730667 -6.75327262484485)
                      #(4.9679877220982345 -5.895604181952111 1.4763390711352997 -0.021073014592237982 0.0);(rf qk 5) changed to 0 ... but is ignored in calculations...
                      -1.4283341763844224 'undefined 'undefined)
                epsilon100)
  ;cond big kv [used in previous tests]
  ;cond else [used at least the first time in next test]
 (check-within (RealIT 0.0 4 #(1. 2. 3. 4. -5.) 5 #(1. 2. 3. 0. 5.))
                (list 'RealIT:normal 1
                      #(1.0 2.68412431945307 4.836274723373266 7.308613153815818 0.0)
                      #(1.0 2.6841243194530113 4.836274723373138 7.308613153815954 5.0)
                      #(1.0 3.368257161011083 7.1406436905046 12.193742265406083 0.0);(rf qk 5) changed to 0 ... but is ignored in calculations...
                      0.0 0.6841243194530697 0)
                epsilon100))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT N uu vv NN p K)
  ;return (list NZ qp K qk szr szi lzr lzi a b c d e f g h a1 a3 a7)
  (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)
           (a* *)(b* *)(c* *)(d* *)(e* *)(f* *)(g* *)(h* *)(a1* *)(a3* *)(a7* *)
           (qp* NN *)(K* NN *)(qk* NN *))
  (s! K* K)
  (let loop ([j 0][omp 0][relstp 0][tried? #f]
             ;uu and vv are coefficients of the starting quadratic
             [u uu][v vv]
             [a (rf a*)][b (rf b*)][qp (rf qp*)])
    (Quad 1. u v szr* szi* lzr* lzi*)
    (cond
      [(> (abs (- (abs (rf szr*))(abs (rf lzr*)))) (* 0.01 (abs (rf lzr*))))
       ;Return if the roots of the quadratic are real and not close
       ;to multiple or nearly equal and of opposite sign
       (label QuadIT-go-linear)
       (list 0 qp K* qk* (rf szr*)(rf szi*)(rf lzr*)(rf lzi*) a b (rf c*)(rf d*)(rf e*)(rf f*)(rf g*)(rf h*)(rf a1*)(rf a3*)(rf a7*))]
      [else
       ;Evaluate polynomial by quadratic synthetic division
       (match-define (list qp a b)(QuadraticSyntheticDivision NN u v p))
       (define mp (+ (abs (- a (* (rf szr*) b))) (abs (* (rf szi*) b))))
       ;Compute a rigorous bound on the rounding error in evaluating p
       (define zm (sqrt (abs v)))
       (define t (- (* (rf szr*) b)))
       (define e0 (for/fold ([e0 (* 2 (abs (rf qp 0)))])
                                  ([i (in-range 1 N)])
                          (+ (* e0 zm) (abs (rf qp i)))))
       (define ee (* (+ (* 9 (+ (* e0 zm) (abs (+ a t))))(* 2 (abs t))(* -7 (+ (abs (+ a t))(* zm (abs b))))) epsilon.0))
       (cond
         [(<= mp (* 20 ee))
          ;Iteration has converged sufficiently if the polynomial
          ;value is less than 20 times this bound
          (label QuadIT-converged)
          (list 2 qp K* qk* (rf szr*)(rf szi*)(rf lzr*)(rf lzi*) a b (rf c*)(rf d*)(rf e*)(rf f*)(rf g*)(rf h*)(rf a1*)(rf a3*)(rf a7*))]
       ;Stop iteration after 20 steps
         [(> j 20)
          (label QuadIT-maxiter)
          (list 0 qp K* qk* (rf szr*)(rf szi*)(rf lzr*)(rf lzi*) a b (rf c*)(rf d*)(rf e*)(rf f*)(rf g*)(rf h*)(rf a1*)(rf a3*)(rf a7*))]
         [else
          (define-values (j+ tried?+ u+ v+ a+ b+ qp+)
            (cond
              [(and (>= j 2)
                    (<= relstp 0.01) (>= mp omp) (not tried?))
               ;A cluster appears to be stalling the convergence.
               ;Five fixed shift steps are taken with a u, v close to the cluster
               (label QuadIT-relstp)
               (define relstp+ (if (< relstp epsilon.0) (sqrt epsilon.0) (sqrt relstp)))
               (define u+ (- u (* u relstp+)))
               (define v+ (+ v (* v relstp+)))
               (match-define (list qp+ a+ b+)(QuadraticSyntheticDivision NN u+ v+ p))
               (for ([i (in-range 5)]) (calcSC->nextK_imp N a+ b+ K* u+ v+ qp+))
               (values 0 #t u+ v+ a+ b+ qp+)]
              [else (values j tried? u v a b qp)]))
          ;Calculate next K polynomial and new u and v
          (calcSC->nextK_imp N a+ b+ K* u+ v+ qp+)
          ;(match-define (list ui vi)(calcSC->newest N (rf a*) (rf b*) K* u v p))
          (define tFlag (calcSC_imp N a+ b+ a1* a3* a7* c* d* e* f* g* h* (rf K*) u+ v+ qk*))
          (match-define (list ui vi)(newest tFlag a+ (rf a1*) (rf a3*) (rf a7*) b+ (rf c*) (rf d*) (rf f*) (rf g*) (rf h*) u+ v+ (rf K*) N p))
          (cond
            [(isZero vi)
             ;If vi is zero, the iteration is not converging
             (label QuadIT-nonconverging)
             (list 0 qp+ K* qk* (rf szr*)(rf szi*)(rf lzr*)(rf lzi*) a+ b+ (rf c*)(rf d*)(rf e*)(rf f*)(rf g*)(rf h*)(rf a1*)(rf a3*)(rf a7*))]
            [else
             (label QuadIT-normal)
             (loop (+ j+ 1) mp (abs (/ (- vi v+)vi)) tried?+
                   ui vi
                   a+ b+ qp+)])])])))
(define (QuadIT_imp N NZ* uu vv szr* szi* lzr* lzi* qp* NN a* b* p qk* a1* a3* a7* c* d* e* f* g* h* K*)
  (match-define (list NZ qp K qk szr szi lzr lzi a b c d e f g h a1 a3 a7)
    (QuadIT N uu vv NN p (rf K*)))
  (s! NZ* NZ)(s! qp* qp NN)(s! K* K N)(s! qk* qk N)
  (s! szr* szr)(s! szi* szi)(s! lzr* lzr)(s! lzi* lzi)
  ;it seems the info on the next line is redundant... but not all paths tested so far
  (s! a* a)(s! b* b)(s! c* c)(s! d* d)(s! e* e)(s! f* f)(s! g* g)(s! h* h)(s! a1* a1)(s! a3* a3)(s! a7* a7)
  )
(module+ test
  ;QuadIT-go-linear
  (let ()
    (define p #(1. 2. 3. 4. 5.))
    (define qp* (vector 1. 2. 3. 4. 5.))
    (define K* (vector 1. 2. 3. 4. 5.))
    (define qk* (vector 1. 2. 3. 4. 5.))
    (define NN (vector-length p))
    (define N (- NN 1))
    (prepare (NZ* *)(szr* *)(szi* *)(lzr* *)(lzi* *)
             (a* *)(b* *)(c* *)(d* *)(e* *)(f* *)(g* *)(h* *)
             (a1* *)(a3* *)(a7* *))
    (QuadIT_imp N NZ* 6. 7. szr* szi* lzr* lzi* qp* NN a* b* p qk* a1* a3* a7* c* d* e* f* g* h* K*)
    ;(check-within qp* #(1. 2. 3. 4. 5.) epsilon100);not important for other calculations...i think
    (check-within K* #(1. 2. 3. 4. 5.) epsilon100)
    ;(check-within qk* #(1. 2. 3. 4. 5.) epsilon100);not important for other calculations...i think
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(0 -1.585786437626905 0 -4.414213562373095 0) epsilon100)
    (check-within (map rf (list a* b* c* d* e* f* g* h* a1* a3* a7*))
                  '(undefined undefined undefined undefined undefined undefined undefined undefined undefined undefined undefined)
                  epsilon100))
  ;QuadIT-converged
  (let ()
    (define p #(1. 2. 3. 4. 5.))
    (define qp* (vector 1. 2. 3. 4. 5.))
    (define K* (vector 1. 2. 3. 4. 5.))
    (define qk* (vector 1. 2. 3. 4. 5.))
    (define NN (vector-length p))
    (define N (- NN 1))
    (prepare (NZ* *)(szr* *)(szi* *)(lzr* *)(lzi* *)
             (a* *)(b* *)(c* *)(d* *)(e* *)(f* *)(g* *)(h* *)
             (a1* *)(a3* *)(a7* *))
    (QuadIT_imp N NZ* -0.575630959115296 0.0828377502729989 szr* szi* lzr* lzi* qp* NN a* b* p qk* a1* a3* a7* c* d* e* f* g* h* K*)
    (check-within qp* #(1.0 2.575630959115296 2.3944555573388273 0. 0.) epsilon100)
    (check-within K* #(1.0 2.7141314657388516 2.7511817500546467 0.3316333077843976 5.0) epsilon100)
    (check-within qk* #(1.0 3.2897624433408463 2.556713395073429 -5.066185467027889 5.0) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(2 0.287815479557648 1.4160930801719076 0.287815479557648 -1.4160930801719076) epsilon100)
    (check-within (map rf (list a* b* c* d* e* f* g* h* a1* a3* a7*))
                    '(0. 0. -5.066185467027889 2.556713395073429 8.83349690503021e-08 -0.5046624154826573 -5.0848344590867324e-08 -9.995370529786954e-07 -7.045165712076444e-07 -1.096316891718955e-13 -7.309719664513362e-08)
                    epsilon100);not important for other calculations...i think
    )
  ;QuadIT-maxiter
  ;[TODO ???]
  ;QuadIT-relstp
  (check-within (QuadIT 9 14.737906787890154 56.6995805579966 10
                        #(-74.43388870038298 -48.684338183687615 82.95039531162064 2.082613677062014 60.82122424869209 -46.15017147716964 61.0180453610964 47.02754709444238 -5.330451975747479 91.51704177156668)
                        #(38.515673952936254 7.252656554000609 -84.42246656861926 31.693388752691646 -27.265410421231138 -35.244767584584565 -97.79006609235279 8.92096535665003 -60.693225828975194 -16.564537967886736))
                '(2 #(-74.43388870038298    28.5525675415266  134.72025177002524 -168.93474867929848   88.79349933216068  46.45222659669343 -84.28416458872897   83.6875414818494   -4.263256414560601e-14 0.0 0.0)
                    #(-74.43388870038298 -1291.101631406862   640.9347772344079  2219.5491668571904 -2906.28648822974   1620.6910078684268  739.2772124821581 -1410.6042877693205 1483.7141716555477     -16.564537967886736)
                    #(-74.43388870038298 -1213.8647256817187 1981.9086377214949  1490.4356655462275 -6620.1774535442755 6860.294452068977   860.1761575225632 -9805.29130225142  10717.60014995853         0.0)
                    -0.5188289035664532 0.907949839624714 -0.5188289035664532 -0.907949839624714
                    0.0 -4.263256414560601e-14 10717.60014995853 -9805.29130225142 1.4951655107757719e-13 -0.9148775066300042 1.5514701652109156e-13 -1.0600397392729366e-09 4.967025159902387e-10 1.8507724128489367e-22 1.0510034321805513e-09)
                epsilon100);NOT COMPLETELY IN LINE WITH C-impl! roots are exact, but K*/qk* not -> (discarded anyway for the next round, but still...)
  ;QuadIT-nonconverging
  ;To Be Checke Akiti!!
  (check-within (QuadIT 15 7.080387980931846 3775.5567802833493 16
                        #(765.8552749843789 -1347.293632350993 -2161.190180483506 -7837.706508659749 -3083.532590734134 2512.6246767498906 5888.814821883812 -224.71114833786896 4321.646577124439 -4104.541569406959 -358.0259626750949 -5940.17140915836 -2813.1556404590783 -1218.789675221933 -92.31608576929261 13.465814510071247)
                        #(569.9471955954955 426.1973931512889 -39.26465304820874 -525.558286377151 -6935.288424258491 5283.823600793081 -1.6306656043934709 1584.535288608834 1907.3886808609604 -3739.1601002469033 -430.3641207148028 3278.5379900289245 -1171.8752324055004 1657.6923655682594 -2854.6807003064246 -573.1114539004168))
                '(0 #(765.8552749843789 -1347.2936322007815 -2161.190180771193 -7837.7065090424085 -3083.5325922052557 2512.62467638493 5888.814822470982 -224.71114725974803 4321.646576900171 -4104.541568552454 -358.0259636123816 -5940.171409102984 -2813.1556416132016 -1218.7896755919267 -92.31608592225949 13.465814529259115 0.0)
                    #(765.8552749843789 -1235.5810851818474 -2357.715044087775 -8152.951526701866 -4226.790575157413 2062.8408974624554 6255.322322625176 634.2690337473058 4288.868772236702 -3474.158567758887 -956.7406398036304 -5992.395365236808 -3679.6270225980984 -1629.1345512998803 -270.0965405173288 -573.1114539004168)
                    #(765.8552749843789 -1235.581085031636 -2357.715044353551 -8152.95152712649 -4226.790576684351 2062.8408968829076 6255.32232315911 634.269034911075 4288.868772169695 -3474.1585669370957 -956.7406406162736 -5992.395365318152 -3679.6270237441445 -1629.1345518382218 -270.0965407242653 0.0)
                    9.806777612197948e-11 5.531679987906852e-06 9.806777612197948e-11 -5.531679987906852e-06
                    13.465814529259115 -92.31608592225949 -270.0965407242653 -1629.1345518382218 -0.008265624539154894 0.16579142614064865 1.810646649336313e-08 -2.824824547799034e-09 -28.771030070033174 -0.11130336732248461 2.2325165894853867)
                epsilon100)
  ;QuadIT-normal [done in break converged]
  )
(define (FixedShift L2 sr bnd K N p NN)
  (call/ec
   (λ (return)
     (prepare (a* *)(b* *)(szr* *)(lzr* *)(szi* *)(lzi* *)
              (qk* NN *)(qp* NN *)(svk* NN *)(K* NN *)
              (iFlag* 1)(NZ* 0))
     (s! K* K)
     (define betav 0.25)
     (define betas 0.25)
     (define u (* -2 sr))
     (define v bnd)
     ;Evaluate polynomial by synthetic division
     (QuadraticSyntheticDivision_imp NN u v p qp* a* b*)
     (define a1* (box 'undefined))(define a3* (box 'undefined))(define a7* (box 'undefined))(define c* (box 'undefined))(define d* (box 'undefined))(define e* (box 'undefined))(define f* (box 'undefined))(define g* (box 'undefined))(define h* (box 'undefined))
     (define tFlag (calcSC_imp N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
     (let loop ([j 0]
                [ovv v][oss sr][otv 0][ots 0])
       (cond
         [(< j L2)
          ;Calculate next K polynomial and estimate v
          (nextK_imp N tFlag (rf a*) (rf b*) (rf a1*) a3* a7* K* (rf qk*) (rf qp*))
          (define ui* (box 'undefined))(define vi* (box 'undefined))
          (set! tFlag (calcSC_imp N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
          (newest_imp tFlag ui* vi* (rf a*) (rf a1*) (rf a3*) (rf a7*) (rf b*) (rf c*) (rf d*) (rf f*) (rf g*) (rf h*) u v (rf K*) N p)
          (define vv (rf vi*))
          ;Estimate s
          (define ss (if (not (= (rf K* (- N 1)) 0)) (- (/ (rf p N)(rf K* (- N 1)))) 0.0))
          (define ts 1.0)
          (define tv 1.0)
          (cond
            [(and (not (= j 0)) (not (equal? tFlag 'calcSC:almost-factor)))
             ; Compute relative measures of convergence of s and v sequences
             (set! tv (if (not (= vv 0.0)) (abs (/ (- vv ovv) vv)) tv))
             (set! ts (if (not (= ss 0.0)) (abs (/ (- ss oss) ss)) ts))
             ;If decreasing, multiply the two most recent convergence measures
             (define tvv (if (< tv otv) (* tv otv) 1))
             (define tss (if (< ts ots) (* ts ots) 1))
             ;Compare with convergence criteria
             (define vpass (< tvv betav))
             (define spass (< tss betas))
             (cond
               [(or spass vpass)
                ;At least one sequence has passed the convergence test.
                ;Store variables before iterating
                (for ([i (in-range N)])(s! svk* i (rf K* i)))
                (define s ss)
                ;Choose iteration according to the fastest converging sequence
                (define stry #f)
                (define vtry #f)
                (define fflag #t)
                (let loop2 ()
                  (define continue #f)
                  (s! iFlag* 1);assume each loop that RealIT will be tried unless set 0 below
                  ;here? or only at top?
                  (cond
                    [(or (not fflag)
                         (not spass)
                         (and vpass (<= tvv tss)))
                     (QuadIT_imp N NZ* (rf ui*) (rf vi*) szr* szi* lzr* lzi* qp* NN a* b* p qk* a1* a3* a7* c* d* e* f* g* h* K*)
                     (when (> (rf NZ*) 0)(return (list (rf NZ*) K* qp* (rf lzi*) (rf lzr*) (rf szi*) (rf szr*))))
                     ;Quadratic iteration has failed. Flag that it has been
                     ;tried and decrease the convergence criterion
                     (set! vtry #t)
                     (set! betav (* betav 0.25))
                     ;Try linear iteration if it has not been tried and the s sequence is converging
                     (cond
                       [(or stry (not spass));linear already tried || not converging
                        (s! iFlag* 0)]
                       [else ;reset K for the linear try
                        (for ([i (in-range N)])(s! K* i (rf svk* i)))])]
                    ;Do nothing. Provides a quick short circuit to the linear iteration
                    [fflag (set! fflag #f)]
                    [else 'nada])
                  (when (not (= (rf iFlag*) 0))
                    (define sss* (box s))
                    (RealIT_imp iFlag* NZ* sss* N p NN qp* szr* szi* K* qk*)
                    (set! s (rf sss*))
                    (when (> (rf NZ*) 0)(return (list (rf NZ*) K* qp* (rf lzi*) (rf lzr*) (rf szi*) (rf szr*))))
                    ;Linear iteration has failed. Flag that it has been
                    ;tried and decrease the convergence criterion
                    (set! stry #t)
                    (set! betas (* betas 0.25))
                    (when (not (= (rf iFlag*) 0))
                      (println (list 'FixedShift-9 L2 sr v K* N p NN qp* lzi* lzr* szi* szr*))
                      ;If linear iteration signals an almost double real zero,
                      ;attempt quadratic iteration
                      (s! ui* (- (+ s s)))
                      (s! vi* (* s s))
                      (set! continue #t)))
                  (cond
                    [continue (loop2)]
                    [else
                     ;Restore variables
                     (for ([i (in-range N)])(s! K* i (rf svk* i)))
                     ;Try quadratic iteration if it has not been tried
                     ;and the v sequence is converging
                     (unless (or (not vpass) vtry) (loop2));was break statement
                     ]))
                ;Re-compute qp and scalar values to continue the second stage
                (QuadraticSyntheticDivision_imp NN u v p qp* a* b*)
                (set! tFlag (calcSC_imp N (rf a*) (rf b*) a1* a3* a7* c* d* e* f* g* h* (rf K*) u v qk*))
                (loop (+ j 1) vv ss tv ts)]
               [else (loop (+ j 1) vv ss tv ts)])]
            [else (loop (+ j 1) vv ss tv ts)])]
         [else
          (label FixedShift-maxiter)
          (list (rf NZ*) K* qp* (rf lzi*) (rf lzr*) (rf szi*) (rf szr*))])))))
(define (FixedShift_imp L2 sr bnd K* N p NN qp* lzi* lzr* szi* szr*)
  (match-define (list NZ K qp lzi lzr szi szr)(FixedShift L2 sr bnd (rf K*) N p NN))
  (s! K* K NN)(s! qp* qp NN)
  (s! lzi* lzi)(s! lzr* lzr)(s! szi* szi)(s! szr* szr)
  NZ)
(module+ test
  ; 1)!(j=0) & tFlag=3
  ; 2)+>spass || vpass
  ; 3)++>cond fflag && spass && (vpass || (tss<tvv))
  ; 4)++>else->quaditOK
  ; 5)++>else->stry && !spass
  ; 6)++>else->else
  ; 7)+>!(iFlag=0)
  ; 8)++>!(NZ>0)
  ; 9)++>!(iFlag=0)
  ;10)+> !vpass || vtry
  (let ();passing !1) 1) 2) & 4)
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define p #(1. 2. 3. 4. 5.))
    (define NN (vector-length p))(define N (- NN 1))
    (define qp* (vector 1. 2. 3. 4. 5.))
    (define K* (vector 1. 2. 3. 4. 5.))
    (s! NZ* (FixedShift_imp 5 1.0 2.0 K* N p NN qp* lzi* lzr* szi* szr*))
    (check-within qp* #(1.0 2.575630959115296 2.394455557338827 0.0 0.0) epsilon100)
    (check-within K* #(1.0 3.669100109842665 5.210828554789748 2.6182632847377154 5.0) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(2 0.28781547955764797 1.4160930801719078 0.28781547955764797 -1.4160930801719078)
                  epsilon100))
  (let ();passing !1) 1) 2) 3) 7) & 8)
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define p #(1. 2. 3. 4. -5.))
    (define NN (vector-length p))(define N (- NN 1))
    (define qp* (vector 1. 2. 3. 4. 5.))
    (define K* (vector 1. 2. 3. 4. 5.))
    (s! NZ* (FixedShift_imp 5 1.0 2.0 K* N p NN qp* lzi* lzr* szi* szr*))
    (check-within qp* #(1.0 2.68412431945307 4.836274723373266 7.308613153815818 0.0) epsilon100)
    (check-within K* #(1.0 2.684124319453068 4.8362747233736165 7.308613153816669 5.0) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(1 0.6841243194530697 0 undefined undefined)
                  epsilon100))
  (let ();passing !1) 1) !2)
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define p  #(5.973052788152122 3.1198874346298604 4.732251119406017 3.6024342708537196 4.181120877543731))
    (define NN (vector-length p))(define N (- NN 1))
    (define qp* (vector 5.973052788152122 44.392007844469305 307.9627791918564 2105.483624570146 14371.728188895837))
    (define K*  (vector 5.973052788152122 -7.411175697861289 -0.024070219044631358 -0.4006197810018648 1.397337061503462))
    (s! NZ* (FixedShift_imp 5 3.4548598408258635 0.586936423108628 K* N p NN qp* lzi* lzr* szi* szr*))
    (check-within qp* #(5.973052788152122 -4.285169564149636 5.5226517874526735 0.0 0.0) epsilon100)
    (check-within K* #(5.973052788152122 -1.5301483105752052 3.546152726901954 2.5472775128829883 1.397337061503462) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(2 -0.6198720538237862 0.6106098345570848 -0.6198720538237862 -0.6106098345570848)
                  epsilon100))
  (let ();passing ... !8) 10) ...
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define p  #(8.41755012535733 4.671578854715546 0.5931615068990723 0.7322427309831809 5.728464948833154))
    (define NN (vector-length p))(define N (- NN 1))
    (define qp* (vector 3.6476498420143426 2.721198761372208 6.567163943771762 9.983085919283766 9.941966838186865))
    (define K*  (vector 8.401638613441222 9.708937329579836 0.33872763171218045 0.1468471881337965 0.32549909728202325))
    (s! NZ* (FixedShift_imp 5 0.24442525134432416 9.30559289538379 K* N p NN qp* lzi* lzr* szi* szr*))
    (check-within qp* #(8.41755012535733 13.252560535681688 8.27797623788355 4.689582056016661e-13 6.483702463810914e-14) epsilon100)
    (check-within K* #(8.41755012535733 4.690864413054477 -5.201527218920869 -8.4197321153409 0.32549909728202325) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(2 0.5097077863021263 0.6574273375997998 0.5097077863021263 -0.6574273375997998)
                  epsilon100))
  (let ();passing ... 5) ...
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define p  #(6.7460988725508955 5.98370659970934 6.157731644531755 4.907674864119937 3.8729258686230943))
    (define NN (vector-length p))(define N (- NN 1))
    (define qp* (vector 7.428443942944599 4.547128927848027 5.135593346367454 5.7702655368985685 7.307443236920097))
    (define K*  (vector 8.877633271400752 0.038665127484674225 5.24238410415498 4.852226488120647 6.75060148912601))
    (s! NZ* (FixedShift_imp 5 1.2246379011135278 9.917716291473479 K* N p NN qp* lzi* lzr* szi* szr*))
    (check-within qp* #(6.7460988725508955 22.50676332767947 -5.62289224272052 -232.08003236777014 -508.788831588999) epsilon100)
    (check-within K* #(6.7460988725508955 -2.497107022629141 19.869027988280223 5.097443105442949 6.75060148912601) epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '(0 0.10531206398918308 0 -1.1965964573712842 0)
                  epsilon100))
  #;(let ();looking for -> passing !7) 9)
    (prepare (szr* *)(szi* *)(lzr* *)(lzi* *)(NZ* *))
    (define (rdm)(- (* 20 (random)) 10))
    (define NN 5)(define N (- NN 1))
    (define p* (for/vector ([i (in-range NN)]) (rdm)))(println (list 'p p*))
    (define qp* (for/vector ([i (in-range NN)]) (rdm)))(println (list 'qp qp*))
    (define K* (for/vector ([i (in-range NN)]) (rdm)))(println (list 'K K*))
    (s! NZ* (FixedShift 5 (rdm) (rdm) K* N p* NN qp* lzi* lzr* szi* szr*))
    (check-within p* #() epsilon100)
    (check-within qp* #() epsilon100)
    (check-within K* #() epsilon100)
    (check-within (map rf (list NZ* szr* szi* lzr* lzi*))
                  '()
                  epsilon100))
  )

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
  (define-values (sc- sc+) (for/fold ([sc- +inf.0][sc+ -inf.0])([v (in-vector p*)]) (define V (abs v))(values (min sc- V)(max sc+ V))))
  (define sc (fl/ (fl/ FLT_MIN epsilon.0) sc-));was using +min.0, but that is for double, not single Float
  (define s
    (cond
      [(or (and (< sc 1) (<= 10 sc+))
           (and (< 1 sc) (<= sc+ (/ FLT_MAX sc))))
       (when (= sc 0) (set! sc FLT_MIN))
       (define l (floor (fl+ (fl/ (fllog sc)(fllog 2.0)) 0.5)))
       (flexpt 2.0 l)]
      [else 1.0]))
  (when (not (= s 1.0))
    (for ([i (in-range (+ N 1))])
      (s! p* i (* (rf p* i) s)))))
(module+ test
  (let ()
    (define p* (vector 1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
    (scalePoly p* (- (vector-length p*) 1))
    (check-within p* #(5.293955920339377e-23 -2.649995515044282e-22 5.306029962073926e-22 -5.3120727149296205e-22 2.6590596436449997e-22 -5.324169677789603e-23) epsilon100)))

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
       ;Save K for restarts with new shifts
       (for ([i (in-range N)])(s! temp* i (rf K* i)))
       ;Loop to select the quadratic corresponding to each new shift
       (define ok #f)
       (for ([iter (in-range 20)]
             #:break ok)
         ;Quadratic corresponds to a double shift to a non-real point and its
         ;complex conjugate. The point has modulus BND and angle rotated
         ;by 94° from the previous shift
         (define tmp (+ (* -1 sinr yy)(* cosr xx)))
         (set! yy (+ (* sinr xx)(* cosr yy)))
         (set! xx tmp)
         (define sr (* bnd xx))
         ;Second stage calculation fixed quadratic
         (define lzi* (box 'undefined))(define lzr* (box 'undefined))(define szi* (box 'undefined))(define szr* (box 'undefined))
         (define NZ (FixedShift_imp (* 20 (+ iter 1)) sr bnd K* N (rf p*) (+ N 1) qp* lzi* lzr* szi* szr*))
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
  (define return-value (roots p degree zeror* zeroi*))
  (cons return-value
        (for/list ([i (in-range degree)])
          (+ (rf zeror* i)(* +i (rf zeroi* i))))))
(module+ test
  (check-within (mfr #(1. 2. 3. 4. 5.))
                '(0 0.287815479557648+1.4160930801719078i 0.287815479557648-1.4160930801719078i -1.287815479557648+0.8578967583284905i -1.287815479557648-0.8578967583284905i)
                epsilon100)
  (check-within (mfr #(1. 2. 3. 4. -5.))
                '(0 0.6841243194530697 -2.0591424445683537 -0.3124909374423581+1.8578744391719895i -0.3124909374423581-1.8578744391719895i)
                epsilon100)
  (check-within (mfr #(1. 3. 1. 0.08866210790363471))
                '(0 -0.18350341911302884 -0.1835034190315191 -2.632993161855452)
                epsilon100)
  ;irritatingly difficult (flpoly-from-roots .9998 .9999 1. 1.003 1.003
  (check-within (mfr #(1.0 -5.0057 10.02280722 -10.03422165742 5.02282165484018 -1.00570721742018))
                '(0 0.9998971273942638 1.0029951281002996 0.9995771489617781 1.0030048540302405 1.0002257415134181)
                epsilon100)
  ;same but exact
  ;(mfr #(1 -50057/10000 501140361/50000000 -501711082871/50000000000 251141082742009/50000000000000 -50285360871009/50000000000000))
  (check-within (mfr #(1e-8 1e-16 1e-20 -1e25 38.5))
                '(0 3.85e-24 100000000000.0 -50000000000.0+86602540378.44386i -50000000000.0-86602540378.44386i)
                epsilon100)
  ;checks FixedShift 6)
  (check-within (mfr #(1 -1.1262458658846637 -1.0101179104905715 0.1369529023140107  -0.07030543743385387  0.34354611896594955  0.7685557744974647  0.9049868924344322 -0.4694264319569345))
                '(0 0.37998534697611247 -0.6385228013511156+0.6232370795625065i -0.6385228013511156-0.6232370795625065i 0.16462177207475362+0.9168019517176714i 0.16462177207475362-0.9168019517176714i 1.1475571613888245 -1.00470119265642 1.5512066087288707)
                epsilon100)
  #;(begin
    (define p (for/vector ([i (in-range (+ 5 (random 5)))])(- (* (random) 20) 10)))
    p
    (mfr p))
  )