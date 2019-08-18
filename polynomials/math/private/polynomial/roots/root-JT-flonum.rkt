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
(require "../poly-flonum.rkt"
         "root-helpers.rkt"
         "root-bounds.rkt"
         "root-closedform.rkt")

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
                (struct-copy flresult R
                             [iterations (+ (flresult-iterations R) i)]
                             [iteration-values (append (flresult-iteration-values R) lst)])]
               [(R R-old)
                (flresult-update-iterations R (flresult-iterations R-old)
                                            (flresult-iteration-values R-old))]))

(define (flreal [s : Number]) : Flonum (fl (real-part s)))
(define (flimag [s : Number]) : Flonum (fl (imag-part s)))

(define ϕ (make-polar 1 0.8552113334772213))
(define Δϕ (make-polar 1 1.6406094968746698))
;angles not really important, as long as within FshiftN multiples you don't visit the same value
(define (JenkinsTraub-flroot [P : flpoly]
                             ;JT is supposed to find roots from lowest magnitude to bigger ones roots-mod-lower-bound
                             [x_0 : (U Number (List Number Number)) (* ϕ (roots-mod-lower-bound P))]
                             #:checkΔ [Δfct : EndFct Ward-endfct]
                             #:iterations [iterations : Positive-Integer 20]
                             #:poly-eval [Peval : cPevaluator complexHorner]
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
    (let loop : (Values flpoly Number (flresult Number)(U 'quadratic 'linear 'no-convergence))
      ([i : Positive-Integer 1]
       [s : Number r0]
       [Ki : flpoly K1]
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

  (flresult-update-iterations
   (case convergence
     [(no-convergence) rslt2]
     [(linear)
      (linear-shift LshiftN s2 P K2 Peval Δfct #f QshiftN)]
     [(quadratic)
      (quadratic-shift QshiftN s2 P K2 Peval Δfct #f LshiftN)])
   rslt2))

;------------------------------------
;stage 1 0 shifts : generating K-poly's x-scaled around 0
;------------------------------------
(: zero-shift (->* (Nonnegative-Integer flpoly) (flpoly) flpoly))
(define (zero-shift iterations P [K (flpoly*s (flpoly-diff P) (/ 1.0 (flpoly-degree P)))]) : flpoly
;(println (list 'Zero-shift P K))
  (define -p0 (fl* -1.0 (flpoly-coefficient P 0)))
  (define P- (flpoly-shift P -1)); equal to (P(x)-P(0))/x
  (for/fold ([Ki K])
            ([i (in-range iterations)])
    (flpoly+ (flpoly-shift Ki -1)
             (flpoly*s P- (fl/ (flpoly-coefficient Ki 0) -p0)))))

(: zero-shift* (->* (Nonnegative-Integer flpoly) (flpoly) flpoly))
(define (zero-shift* iterations P [K (flpoly*s (flpoly-diff P) (/ 1.0 (flpoly-degree P)))])
  (define p0 (flpoly-coefficient P 0))
  (define p1 (flpoly-coefficient P 1))
  (define P- (flpoly-shift P -1))
  (for/fold ([Ki K])
            ([i (in-range iterations)])
    (define k0 (flpoly-coefficient K 0))
    (cond
      [(<= k0 (* (abs p1) 1e-16 10)) (flpoly-shift Ki -1)]
      [else (flpoly+ (flpoly*s (flpoly-shift Ki -1) (- (/ p0 k0))) P-)])))

;------------------------------------
;stage 2 fixed shifts : generating K-poly's x-scaled around (fixed) s
;------------------------------------
(define (fixed-shift [iterations : Nonnegative-Integer]
                     [s : Number]
                     [P : flpoly]
                     [K : flpoly]) : (Values flpoly (flresult Number)(U 'quadratic 'linear 'no-convergence))
;(println (list 'fixed-shift iterations s P K))
  (define u (fl* 2.0 (fl (real-part s))))
  (define v (fl+ (flexpt (fl (real-part s)) 2.0)(flexpt (fl (imag-part s)) 2.0)))
  (define S (flpolyV> (vector 1.0 u v)))
  (define-values (QP/S RP/S) (flpoly/p-QR P S))
  (define b (flpoly-coefficient RP/S 1))
  (define a (fl- (flpoly-coefficient RP/S 0) (fl* b u)))
  (define P@s (- a (* b (conjugate s))));short calc for (Peval P s)
  (let loop ([i : Integer 0]
             [tλ-2 : Number 0.0][tλ-1 : Number 0.0]
             [sλ-2 : Number 0.0][sλ-1 : Number 0.0]
             [Ki : flpoly K])
    (cond
      [(< iterations i)
       (values Ki
               (flresult s 'max-iterations i (list (list s P@s)))
               'no-convergence)]
      [else
       (define K* (flpoly*s Ki (fl/ 1.0 (flpoly-coefficient Ki 0))))
       (define-values (QKi/S RKi/S)(flpoly/p-QR K* S))
       (define d (flpoly-coefficient RKi/S 1))
       (define c (fl- (flpoly-coefficient RKi/S 0) (fl* d u)))
       (define K@s (- c (* d (conjugate s))))
       (define S* (nextSigma P K* a b c d u v))
       (define tλ (- s (/ P@s K@s)))
       (define sλ (flpoly-coefficient S* 0))
;(println (list sλ tλ))
       (cond
         [(converged? sλ-2 sλ-1 sλ)
          (values Ki
                  (flresult s 'done i (list (list s P@s)))
                  'quadratic)]
         [(converged? tλ-2 tλ-1 tλ)
          (values Ki
                  (flresult s 'done i (list (list s P@s)))
                  'linear)]
         [else
          (loop (+ i 1)
                tλ-1 tλ sλ-1 sλ
                (nextK-quadratic-shift QP/S QKi/S a b c d u v))])])))

; "Three Stage Variable-Shift Iterations for the Solution of Polynomial Equations
;  With a Posteriori Error Bounds for the Zeros" by M.A. Jenkins, 1969.
;
; NOTE: we assume (flpoly-coefficient S 2) is 1.0.
;a b c d are coefficents of the rest polynomials of P/S (a b) and K/S (c d) see fixed-shift
;u & v are (flpoly-coefficient S 1) & (flpoly-coefficient S 0)
(define (nextSigma [P : flpoly][K : flpoly][a : Flonum][b : Flonum][c : Flonum][d : Flonum][u : Flonum][v : Flonum]) : flpoly
  (define b1 (fl* -1.0 (fl/ (flpoly-coefficient K 0)
                            (flpoly-coefficient P 0))))
  (define b2 (fl* -1.0 (fl/ (fl+ (flpoly-coefficient K 1)
                                 (fl* b1 (flpoly-coefficient P 1)))
                            (flpoly-coefficient P 0))))
  (define a1 (fl- (fl* b c)(fl* a d)))
  (define ua+vb (fl+ (fl* u a)(fl* v b)))
  (define a2 (fl+ (fl* a c)(fl* ua+vb d)))
  (define c2 (fl* b1 a1))
  (define c3 (fl* (fl* b1 b1)(fl+ (fl* a a) (fl* ua+vb b))))
  (define c4 (fl- (fl* v (fl* b2 a1)) (fl+ c2 c3)))
  (define c1 (flsum (list (fl* c c)
                          (fl* u (fl* c d))
                          (fl* v (fl* d d))
                          (fl* b1 (fl+ (fl* a c)
                                       (fl* b (fl+ (fl* u c)(fl* v d)))))
                          (fl* -1.0 c4))))
  (define δu (fl/ (fl+ (fl* u (fl+ c2 c3))
                       (fl* v (fl+ (fl* b1 a1)(fl* b2 a2))))
                  (fl* -1.0 c1)))
  (define δv (fl* v (fl/ c4 c1)))
  (flpoly> 1.0 (fl+ u δu)(fl+ v δv)))

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
(define (nextK-quadratic-shift [QP/S : flpoly][QKi/S : flpoly]
                               [a : Flonum][b : Flonum][c : Flonum][d : Flonum][u : Flonum][v : Flonum])
  (define bc-ad (fl- (fl* b c)(fl* a d)))
  (define ua+vb (fl- (fl* u a)(fl* v b)))
  (define C0 (fl/ (fl+ (fl* a a)(fl* b ua+vb)) bc-ad))
  (define C1 (fl/ (fl+ (fl* a c)(fl* d ua+vb)) bc-ad))
  (flpoly+ (flpoly*s QKi/S C0)
           (flpoly*p (flpoly> 1.0 (fl* -1.0 C1)) QP/S)
           (const-flpoly b)))
;------------------------------------
;stage 3 variable shifts : generating K-poly's x-scaled around (variable) s
;------------------------------------
(define (linear-shift [iterations-Lin : Nonnegative-Integer]
                      [s : Number]
                      [P : flpoly]
                      [K : flpoly]
                      [Peval : cPevaluator]
                      [Δfct : EndFct]
                      [triedQuad? : Boolean]
                      [iterations-Quad : Nonnegative-Integer]) : (flresult Number)
;(println (list 'linear-shift iterations-Lin s P K triedQuad? iterations-Quad))
  (define s0 : Flonum
    (fl (real-part (- s (/ (Peval P s)(Peval K s))))))
  (let loop ([i : Integer 0]
             [si : Flonum s0]
             [Ki : flpoly K]
             [lst : (Listof (List Flonum Flonum)) '()])
    (define-values (P* P@si) (flpoly-reduce-root-QR P si))
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
       (define-values (K* K@si)(flpoly-reduce-root-QR Ki si))
       (define K** (flpoly- K* (flpoly*s P* (/ K@si P@si))))
       (define K*** (flpoly*s K** (/ 1.0 (flpoly-reverse-coefficient K** 0))))
       (define K***@si (Peval K*** si))
       (define Δsi (/ P@si K***@si))
       (define si* (- si Δsi))
       (cond
         [(and (<= 2 i) (not triedQuad?) (< (flabs Δsi) (fl* 0.001 (flabs si*))) (< (flabs (cadar lst)) P@si))
          ;iterations stalling, try for double root with quadrati shift
          (quadratic-shift iterations-Quad si* P K*** Peval Δfct #f iterations-Lin)]
         [else
          (loop (+ i 1) si* K*** lst+)])])))

(define (quadratic-shift [iterations-Quad : Nonnegative-Integer]
                         [s : Number]
                         [P : flpoly]
                         [K : flpoly]
                         [Peval : cPevaluator]
                         [Δfct : EndFct]
                         [triedLin? : Boolean]
                         [iterations-Lin : Nonnegative-Integer]) : (flresult Number)
;(println (list 'quadratic-shift iterations-Lin s P K triedLin? iterations-Lin))
  (define (go-for-lin [si : Number][Ki : flpoly][i : Integer][lst+ : (Listof (List Number Number))]) : (flresult Number)
    (cond
         [triedLin? (flresult si 'max-iterations i lst+)]
         [else
          (flresult-update-iterations
           (linear-shift iterations-Lin si P Ki Peval Δfct #t iterations-Quad)
           i lst+)]))
  (define sR (fl (real-part s)))(define sI (fl (imag-part s)))
  (define S (flpoly> 1.0 (fl* -2.0 sR) (fl+ (fl* sR sR)(fl* sI sI))))
  (let loop ([i : Integer 0]
             [Si : flpoly S]
             [Ki : flpoly K]
             [tryFixedShifts? : Boolean #t]
             [v-1 : Flonum (flpoly-coefficient S 0)]
             [P@s-1 : Flonum 0.0]
             [lst : (Listof (List Number Number)) '()])
    (define u (flpoly-coefficient Si 1))
    (define v (flpoly-coefficient Si 0))
    (define-values (QP/Si RP/Si)(flpoly/p-QR P S))
    (define b (flpoly-coefficient RP/Si 1))
    (define a (fl- (flpoly-coefficient RP/Si 0) (fl* b u)))
    (define sis (flpoly-2°root Si))
    (define-values (s0 s1)
      (if (< (magnitude (car sis))(magnitude (cadr sis)))
          (values (car sis)(cadr sis))
          (values (cadr sis)(car sis))))
    (define P@s (fl+ (flabs (fl- a (fl* (flreal s0) b)))
                     (flabs (fl* (flimag s0) b))))
    (define lst+ (cons (list s0 P@s) lst))
    (cond
      [(< iterations-Quad i) (go-for-lin s0 Ki i lst+)]
      ;if roots are not close try linear shift
      [(< (* .01 (abs (real-part (car sis))))
          (abs (- (real-part (car sis))(real-part (cadr sis)))))
       ;in c impl. they take the diference of the abs values... why?
       (go-for-lin s0 Ki i lst+)]
      [else
       (define K*1
         (cond
           [(and tryFixedShifts?
                 (< (abs (/ (- v v-1) v)) *kTinyRelStep*)
                 (< P@s P@s-1))
            (define-values (Ki+1 _0 _1) (fixed-shift *innerFixedShiftItereations* s0 Ki P))
            (set! tryFixedShifts? #f)
            Ki+1]
           [else Ki]))
       (define-values (QKi/Si RKi/Si) (flpoly/p-QR K*1 Si))
       (define d (flpoly-coefficient RKi/Si 1))
       (define c (fl- (flpoly-coefficient RKi/Si 0) (fl* d u)))

       (define S* (nextSigma QP/Si QKi/Si a b c d u v))
       (define K*2 (nextK-quadratic-shift QP/Si QKi/Si a b c d u v))
       (define K*3 (flpoly*s K*2 (fl/ 1.0 (flpoly-coefficient K*2 0))))

       (loop (+ i 1) S* K*3 tryFixedShifts? v P@s lst+)])))

;(module+ test
  (define-syntax-rule (show r)
    (let ([R r])
      (printf "------------------\n~a ~a in ~a\n~a\n~a\n\n"
              'r (flresult-endmsg R) (flresult-iterations R)
              (flresult-root R)
              (for/list : (Listof Any) ([l (in-list (flresult-iteration-values R))][i (in-range 5)]) l))))
  (show (JenkinsTraub-flroot (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397)))
  (show (JenkinsTraub-flroot (flpoly-from-roots 1.0 2.0 2.0 3.0)))
  (show (JenkinsTraub-flroot (flpoly< -1.00570721742018 5.02282165484018 -10.03422165742 10.02280722 -5.0057 1.0)))
;)