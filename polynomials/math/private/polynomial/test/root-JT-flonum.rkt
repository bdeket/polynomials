#lang typed/racket/base

#|
This RPOLY implementation is loosely based on the (some variant of)c library
by Chris Sweeney [https://github.com/sweeneychris/RpolyPlusPlus -> src]

General:
P : the polynomial of wich we are trying to find a root
for P with real coefficient if s is a root than (conjugate s) should also be a root

K : shifted/scaled polynomial to seperate the roots of P
Ki+1 is of the form: (Ki(x)-(Ki(si)/P(si))*P(x))/(x-si)
K0 is the first order derivatife of P

S : (sigma) is a polynomial with 2 conjugate roots, one of them the current root we are trying to find
so S with roots s and (conjugate s) has real coefficients too

si+1 = si + P(si)/Ki+1(si)
|#

(require math/flonum
         racket/match
         (only-in racket/math conjugate))
(require "poly-struct.rkt"
         "root-helper.rkt")

(define-type flPoly (Poly Flonum))

(provide JenkinsTraub-flroot)

;maximum absolute tolerance for y=P @ root s, if y is smaller we assume to have found a root
;using the provided checkΔ is not enough because if y becomes to small, K can explode (inf or nan)
(define *K-absolute-tolerance* 1e-14)
(define *innerFixedShiftItereations* 20)
(define *kTinyRelStep* 0.01)

;test convergence of 3 successive delta's
(define (converged? [Δ0 : Number][Δ1 : Number][Δ2 : Number]) : Boolean
  (and (< (magnitude (- Δ1 Δ0))(/ (magnitude Δ0) 2))
       (< (magnitude (- Δ2 Δ1))(/ (magnitude Δ1) 2))))

;update iteration-results
(: flresult-update-iterations (case-> (-> (flresult Number) Integer (Listof (List Number Number)) (flresult Number))
                                      (-> (flresult Number) (flresult Number) (flresult Number))))
(define flresult-update-iterations
  (case-lambda [(R i lst)
                (struct-copy iteration-result R
                             [iterations (+ (iteration-result-iterations R) i)]
                             [values (append (iteration-result-values R) lst)])]
               [(R R-old)
                (flresult-update-iterations R (iteration-result-iterations R-old)
                                            (iteration-result-values R-old))]))

(define (flreal [s : Number]) : Flonum (fl (real-part s)))
(define (flimag [s : Number]) : Flonum (fl (imag-part s)))

;angles not really important, as long as within FshiftN multiples you don't visit the same value
(define ϕ (make-polar 1 0.8552113334772213))
(define Δϕ (make-polar 1 1.6406094968746698))

;temp fcts - need real implementation
(define (roots-mod-lower-bound [P : flPoly]) : Flonum)


(define (root-JT P #:checkΔ) [Δfct : EndFct Ward-endfct])
(define (JenkinsTraub-flroot [P : flPoly]
                             ;JT is supposed to find roots from lowest magnitude to bigger ones roots-mod-lower-bound
                             [x_0 : (U Number (List Number Number)) (* ϕ (roots-mod-lower-bound P))]
                             #:checkΔ [Δfct : EndFct Ward-endfct]
                             #:iterations [iterations : Positive-Integer 20]
                             #:poly-eval [Peval : cPevaluator fl/cHorner]
                             #:zero-shift-iterations [0shiftN : Positive-Integer iterations]
                             #:fixed-shift-tries [FshiftN : Positive-Integer iterations]
                             #:fixed-shift-iteration-multiplier [FshiftN* : Positive-Integer iterations]
                             #:linear-shift-iterations [LshiftN : Positive-Integer iterations]
                             #:quadratic-shift-iterations [QshiftN : Positive-Integer iterations]) : (flresult Number)
  (define r0
    (if (list? x_0)
        (let ([r0 (roots-mod-lower-bound P)])
          (if (<= (magnitude (car x_0)) r0 (magnitude (cadr x_0)))
              (make-polar r0 (/ (+ (angle (car x_0))(angle (cadr x_0)))2))
              (if (< (magnitude (- (car x_0) r0))(magnitude (- (cadr x_0) r0)))
                  (car x_0)
                  (cadr x_0))))
        x_0))
  ;stage 1 : apply zero-shifts to K-polynomial to separate small roots
  (define K1 (zero-shift 0shiftN P))
;(println (list '-> K1))(newline)
  
  ;apply fixed shifts to K-poly to further seperate roots
  (define-values (K2 s2 rslt2 convergence)
    (let loop : (Values flPoly Number (flresult Number)(U 'quadratic 'linear 'no-convergence))
      ([i : Positive-Integer 1]
       [s : Number r0]
       [Ki : flPoly K1]
       [rslt : (flresult Number) (flresult 0 'max-iterations 0shiftN '())])
      (define-values (K* rslt* convergence)(fixed-shift (* i FshiftN*) s P Ki))
      (define rslt** (flresult-update-iterations rslt* rslt))
      (cond
        [(or (equal? (flresult-endmsg rslt*) 'done)
             (< FshiftN i))
         (values K* s rslt** convergence)]
        [else
         (loop (+ i 1) (* s Δϕ) K*
               rslt**)])))
;(println (list '-> K2 s2 convergence))(newline)

  ;do variable shifts
  (flresult-update-iterations
   (case convergence
     [(no-convergence) rslt2]
     [(linear)
      (linear-shift LshiftN s2 P K2 Peval Δfct #f QshiftN)]
     [(quadratic)
      (quadratic-shift QshiftN s2 P K2 Peval Δfct #f LshiftN)])
   rslt2))

;------------------------------------
;P(z)= QP/S * S(z) + b*(z+u)+a
;with s root of S
;P(s)= a - b * s_conj
;P(s_conj)= a - b * s
;------------------------------------
(define (P/S [P : flPoly][S : flPoly])
  (define-values (QP/S RP/S)(flPoly/p-QR P S))
  (values QP/S
          (fl- (flPoly-coefficient RP/S 0) (fl* (flPoly-coefficient RP/S 1) (flPoly-coefficient S 1)))
          (flPoly-coefficient RP/S 1)))


;------------------------------------
;stage 1 - 0 shifts : generating K-poly's x-scaled around 0
;------------------------------------
(: zero-shift (->* (Nonnegative-Integer flPoly) (flPoly) flPoly))
(define (zero-shift iterations P [K (flPoly*s (flPoly-diff P) (/ 1.0 (flPoly-degree P)))])
  (define p0 (flPoly-coefficient P 0))
  (define p1 (flPoly-coefficient P 1))
  (for/fold ([Ki K])
            ([i (in-range iterations)])
    (define k0 (flPoly-coefficient Ki 0))
    (cond
      [(<= (abs k0) (* (abs p1) 1e-16 10)) (flPoly-shift Ki -1)]
      [else (flPoly-shift (flPoly+ P (flPoly*s Ki (- (/ p0 k0)))) -1)])))

;------------------------------------
;stage 2 - fixed shifts : generating K-poly's x-scaled around (fixed) s
;------------------------------------
(define (fixed-shift [iterations : Nonnegative-Integer]
                     [s : Number]
                     [P : flPoly]
                     [K : flPoly]) : (Values flPoly (flresult Number)(U 'quadratic 'linear 'no-convergence))
;(println (list 'fixed-shift iterations s P K))
  (define u (fl* -2.0 (fl (real-part s))))
  (define v (fl+ (flexpt (fl (real-part s)) 2.0)(flexpt (fl (imag-part s)) 2.0)))
  (define S (flPolyV> (vector 1.0 u v)))
  (define-values (QP/S a b)(P/S P S))
  (define P@s (- a (* b (conjugate s))));short calc for (Peval P s)
  (let loop ([i : Integer 0]
             [tλ-2 : Number 0.0][tλ-1 : Number 0.0]
             [sλ-2 : Number 0.0][sλ-1 : Number 0.0]
             [K : flPoly K])
    (cond
      [(< iterations i)
       (values K
               (flresult s 'max-iterations i (list (list s P@s)))
               'no-convergence)]
      [else
       (define K* (flPoly*s K (fl/ 1.0 (flPoly-reverse-coefficient K 0))))
       (define-values (QKi/S c d)(P/S K* S))
       (define K*@s (- c (* d (conjugate s))))
       (define S* (nextSigma P K* a b c d u v))
       (define tλ (- s (/ P@s K*@s)))
       (define sλ (flPoly-coefficient S* 0))
;(println (list sλ tλ))
       (cond
         [(converged? sλ-2 sλ-1 sλ)
          (values K*
                  (flresult s 'done i (list (list s P@s)))
                  'quadratic)]
         [(converged? tλ-2 tλ-1 tλ)
          (values K*
                  (flresult s 'done i (list (list s P@s)))
                  'linear)]
         [else
          (loop (+ i 1)
                tλ-1 tλ sλ-1 sλ
                (nextK-quadratic-shift QP/S QKi/S a b c d u v))])])))

; "Three Stage Variable-Shift Iterations for the Solution of Polynomial Equations
;  With a Posteriori Error Bounds for the Zeros" by M.A. Jenkins, 1969.
;
; NOTE: we assume (flPoly-coefficient S 2) is 1.0.
;a b c d are coefficents based on the rest polynomials of P/S (a b) and K/S (c d) see fixed-shift
;u & v are (flPoly-coefficient S 1) & (flPoly-coefficient S 0)
(define (nextSigma [P : flPoly][K : flPoly][a : Flonum][b : Flonum][c : Flonum][d : Flonum][u : Flonum][v : Flonum]) : flPoly
  (define b1 (fl* -1.0 (fl/ (flPoly-coefficient K 0)
                            (flPoly-coefficient P 0))))
  (define b2 (fl* -1.0 (fl/ (fl+ (flPoly-coefficient K 1)
                                 (fl* b1 (flPoly-coefficient P 1)))
                            (flPoly-coefficient P 0))))
  (define ua+vb (fl+ (fl* u a)(fl* v b)))
  (define a1 (fl- (fl* b c)(fl* a d)))
  (define a3 (fl+ (fl* a a) (fl* ua+vb b)))
  (define a7 (fl+ (fl* a c) (fl* ua+vb d)))
  (define c1 (fl* v (fl* b2 a1)))
  (define c2 (fl* b1 a7));was a1 in c++ file
  (define c3 (fl* (fl* b1 b1) a3))
  (define c4 (fl- c1 (fl+ c2 c3)))
  (define temp (flsum (list (fl* c c)
                            (fl* u (fl* c d))
                            (fl* v (fl* d d))
                            (fl* b1 (fl+ (fl* a c)
                                         (fl* b (fl+ (fl* u c)(fl* v d)))))
                            (fl* -1.0 c4))))
  (define δu (fl/ (fl+ (fl* u (fl+ c2 c3))
                       (fl* v (fl+ (fl* b1 a1)(fl* b2 a7))))
                  (fl* -1.0 temp)))
  (define δv (fl* v (fl/ c4 temp)))
  (flPoly> 1.0 (fl+ u δu)(fl+ v δv)))

; The iterations are computed with the following equation:
;              a^2 + u * a * b + v * b^2
;   K_next =  ___________________________ * QK/S
;                    b * c - a * d
;
;                      a * c + u * a * d + v * b * d
;             +  (z - _______________________________) * QP/S + b.
;                              b * c - a * d
;
; This is done using *only* realy arithmetic so it can be done very fast!
(define (nextK-quadratic-shift [QP/S : flPoly][QK/S : flPoly]
                               [a : Flonum][b : Flonum][c : Flonum][d : Flonum][u : Flonum][v : Flonum])
  (define bc-ad (fl- (fl* b c)(fl* a d)))
  (define ua+vb (fl+ (fl* u a)(fl* v b)))
  (define C0 (fl/ (fl+ (fl* a a)(fl* b ua+vb)) bc-ad))
  (define C1 (fl/ (fl+ (fl* a c)(fl* d ua+vb)) bc-ad))
  ;!!bc-ad=0!!
  (flPoly+ (flPoly*s QK/S C0)
           (flPoly*p (flPoly> 1.0 (fl* -1.0 C1)) QP/S)
           (flPoly-const b)))
;------------------------------------
;stage 3 - variable shifts : generating K-poly's x-scaled around (variable) s
;------------------------------------
; Generate K-Polynomials with variable-shifts that are linear. The shift is
; computed as:
;   K_next(z) = 1 / (z - s) * (K(z) - K(s) / P(s) * P(z))
;   s_next = s - P(s) / K_next(s)
(define (linear-shift [iterations-Lin : Nonnegative-Integer]
                      [s : Number]
                      [P : flPoly]
                      [K : flPoly]
                      [Peval : cPevaluator]
                      [Δfct : EndFct]
                      [triedQuad? : Boolean]
                      [iterations-Quad : Nonnegative-Integer]) : (flresult Number)
;(println (list 'linear-shift iterations-Lin s P K triedQuad? iterations-Quad))
  (define s0 : Flonum
    (fl (real-part (- s (/ (Peval P s)(Peval K s))))))
  (let loop ([i : Integer 0]
             [si : Flonum s0]
             [Ki : flPoly K]
             [lst : (Listof (List Flonum Flonum)) '()])
    (define-values (P* P@si) (flPoly-reduce-root-QR P si))
    ;should it be reevaluated by Peval... why else do we have this function...
    (define lst+ (cons (list si P@si) lst))
    (cond
      [(< iterations-Lin i)
       (cond
         [triedQuad? (flresult si 'max-iterations i lst+)]
         [else
          (flresult-update-iterations
           (quadratic-shift iterations-Quad si P K Peval Δfct #t iterations-Lin)
           i lst+)])]
      [(Δfct lst+) (flresult si 'done i lst+)]
      [(< (abs P@si) *K-absolute-tolerance*)
       ;Kpoly will become unstable if we continue
       (flresult si 'algorithm-stoped i lst+)]
      [else
       ;get new Kpoly
       (define-values (K* K@si)(flPoly-reduce-root-QR Ki si))
       (define K** (flPoly- K* (flPoly*s P* (/ K@si P@si))))
       (define K*** (flPoly*s K** (/ 1.0 (flPoly-reverse-coefficient K** 0))))
       (define K***@si (Peval K*** si))
       (define Δsi (/ P@si K***@si))
       (define si* (- si Δsi))
       (cond
         [(and (<= 2 i) (not triedQuad?) (< (flabs Δsi) (fl* 0.001 (flabs si*))) (< (flabs (cadar lst)) P@si))
          ;iterations stalling, try for double root with quadratic shift
          (quadratic-shift iterations-Quad si* P K*** Peval Δfct #f iterations-Lin)]
         [else
          (loop (+ i 1) si* K*** lst+)])])))

; Generate K-polynomials with variable-shifts. During variable shifts, the
; quadratic shift is computed as:
;                | K0(s1)  K0(s2)  z^2 |
;                | K1(s1)  K1(s2)    z |
;                | K2(s1)  K2(s2)    1 |
;    sigma(z) = __________________________
;                  | K1(s1)  K2(s1) |
;                  | K2(s1)  K2(s2) |
; Where K0, K1, and K2 are successive zero-shifts of the K-polynomial.
;
; The K-polynomial shifts are otherwise exactly the same as Stage 2 after
; accounting for a variable-shift sigma.
(define (quadratic-shift [iterations-Quad : Nonnegative-Integer]
                         [s : Number]
                         [P : flPoly]
                         [K : flPoly]
                         [Peval : cPevaluator]
                         [Δfct : EndFct]
                         [triedLin? : Boolean]
                         [iterations-Lin : Nonnegative-Integer]) : (flresult Number)
;(println (list 'quadratic-shift iterations-Lin s P K triedLin? iterations-Lin))
  (define (go-for-lin [si : Number][Ki : flPoly][i : Integer][lst+ : (Listof (List Number Number))]) : (flresult Number)
(println '(going-for-lin))
    (cond
         [triedLin? (flresult si 'max-iterations i lst+)]
         [else
          (flresult-update-iterations
           (linear-shift iterations-Lin si P Ki Peval Δfct #t iterations-Quad)
           i lst+)]))
  (define sR (fl (real-part s)))(define sI (fl (imag-part s)))
  (define S (flPoly> 1.0 (fl* -2.0 sR) (fl+ (fl* sR sR)(fl* sI sI))))
  (let loop ([i : Integer 0]
             [Si : flPoly S]
             [Ki : flPoly K]
             [tryFixedShifts? : Boolean #t]
             [v-1 : Flonum 0.0]
             [P@s-1 : Flonum 0.0]
             [lst : (Listof (List Number Number)) '()])
    (define u (flPoly-coefficient Si 1))
    (define v (flPoly-coefficient Si 0))
    (define-values (QP/Si a b)(P/S P Si))
    (define sis (flPoly-2°root Si))
    (define-values (s0 s1)
      (if (= 0 (imag-part (car sis)))
          (if (< (abs (real-part (car sis)))(abs (real-part (cadr sis))))(values (car sis)(cadr sis))(values (cadr sis)(car sis)))
          (if (< 0 (imag-part (car sis)))(values (car sis)(cadr sis))(values (cadr sis)(car sis)))))
    (define P@s (fl+ (flabs (fl- a (fl* (flreal s0) b)))
                     (flabs (fl* (flimag s0) b))))
    (define lst+ (cons (list s0 P@s) lst))
    (cond
      [(Δfct lst+)(flresult s0 'done i lst+)]
      [(< iterations-Quad i) (go-for-lin s0 Ki i lst+)]
      ;if roots are not close/imag try linear shift
      [(< (* .01 (abs (real-part s0)))
          (abs (- (abs (real-part s1))(abs (real-part s0)))))
       (go-for-lin s0 Ki i lst+)]
      [else
       (define-values (K*1 tfs?)
         (cond
           [(and tryFixedShifts?
                 (< (abs (/ (- v v-1) v)) *kTinyRelStep*)
                 (< P@s P@s-1))
            (define-values (Ki+1 _0 _1) (fixed-shift *innerFixedShiftItereations* s0 Ki P))
            (values Ki+1 #f)]
           [else (values Ki tryFixedShifts?)]))
       (define-values (QKi/Si c d)(P/S K*1 Si))

       (define S* (nextSigma P K*1 a b c d u v))
       (define K*2 (nextK-quadratic-shift QP/Si QKi/Si a b c d u v))
       (define K*3 (flPoly*s K*2 (fl/ 1.0 (flPoly-coefficient K*2 0))))

       (loop (+ i 1) S* K*3 tryFixedShifts? v P@s lst+)])))

(module+ test
  (define-syntax-rule (show r)
    (let ([R r])
      (printf "------------------\n~a ~a in ~a\n~a\n~a\n\n"
              'r (flresult-endmsg R) (flresult-iterations R)
              (flresult-root R)
              (for/list : (Listof Any) ([l (in-list (flresult-iteration-values R))][i (in-range 5)]) l))))
  (show (JenkinsTraub-flroot (flPoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397)))
  (show (JenkinsTraub-flroot (flPoly-from-roots 1.0 2.0 2.0 3.0)))
  (show (JenkinsTraub-flroot (flPoly< -1.00570721742018 5.02282165484018 -10.03422165742 10.02280722 -5.0057 1.0)))
  (show (JenkinsTraub-flroot (flPoly> 1. 2. 3. 4. 5.)))
)