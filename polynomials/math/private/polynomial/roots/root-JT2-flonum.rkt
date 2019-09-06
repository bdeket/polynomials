#lang typed/racket/base

#|
This RPOLY implementation is loosely based on the (some variant of)c library
by Enrico Bertolazzi [https://github.com/ebertolazzi/quarticRootsFlocke/blob/master/src/PolynomialRoots-Jenkins-Traub.cc]

General:
P : the polynomial of wich we are trying to find a root
for P with real coefficient if s is a root than (conjugate s) should also be a root

K : shifted/scaled polynomial to seperate the roots of P
Ki+1 is of the form: (Ki(x)-(Ki(si)/P(si))*P(x))/(x-si)
K0 is the first order derivatife of P

S : (sigma) is a polynomial with 2 conjugate roots, one of them the current root we are trying to find
so S with roots s and (conjugate s) has real coefficients too

si+1 = si + P(si)/Ki+1(si)

conventie:
R=a+bx
 =c+dx
S=x²+ux+v
|#

(require math/flonum
         racket/match
         (only-in racket/math conjugate))
(require "../poly-flonum.rkt"
         "root-helpers.rkt"
         "root-bounds.rkt"
         "root-closedform.rkt")

(define-type Tflag (U 'almost-factor 'div-d 'div-c))

(define (quadSyntDiv [P : flpoly][u : Flonum][v : Flonum])
  (define-values (P/S-Q P/S-R)(flpoly/p-QR P (flpoly> 1.0 u v)))
  (values P/S-Q (flpoly-coefficient P/S-R 0)(flpoly-coefficient P/S-R 1)))

; This routine calculates scalar quantities used to compute the next
; K polynomial and new estimates of the quadratic coefficients.
; calcSC - integer variable set here indicating how the calculations
; are normalized to avoid overflow.
(define (calcSC [K : flpoly]
                [u : Flonum][v : Flonum]
                [a : Flonum][b : Flonum]) : (List Tflag flpoly (Listof Flonum))
  (define-values (K/S-Q c d)(quadSyntDiv K u v))
  (define h (fl* v b))
  (cond
    [(and (<= (abs c) (* 100 epsilon.0 (abs (flpoly-coefficient K 0))))
          (<= (abs d) (* 100 epsilon.0 (abs (flpoly-coefficient K 1)))))
     (list 'almost-factor K/S-Q '())]
    [(<= (abs c) (abs d))
     (define e (fl/ a d))
     (define f (fl/ c d))
     (define g (fl* u b))
     (define a3 (fl+ (fl* e (fl+ g a)) (fl* h (fl/ b d))))
     (define a1 (fl- (fl* f b) a))
     (define a7 (fl+ h (fl* (fl+ f u) a)))
     (list 'div-d K/S-Q (list a1 a3 a7 c d e f g h))]
    [else
     (define e (fl/ a c))
     (define f (fl/ d c))
     (define g (fl* e u))
     (define a3 (fl+ (fl* e a) (fl* (fl+ g (fl/ h c)) b)))
     (define a1 (fl- b (fl* a f)))
     (define a7 (fl+ (fl* g d) (fl+ (fl* h f) a)))
     (list 'div-c K/S-Q (list a1 a3 a7 c d e f g h))]))

; Computes the next K polynomials using the scalars computed in calcSC
(define (nextK [P/S-Q : flpoly][K/S-Q : flpoly]
               [tflag : Tflag]
               [a : Flonum][b : Flonum][a1 : Flonum][a3 : Flonum][a7 : Flonum]) : (List flpoly Flonum Flonum)
  (case tflag
    [(almost-factor) ; unscaled form of the recurence
     (list K/S-Q a1 a7)]
    [else
     (define temp (if (equal? tflag 'div-c) b a))
     (cond
       [(< (* 10 epsilon.0 (abs temp)) (abs a1)) ; scaled form of the recurence
        (define a3* (fl/ a3 a1))
        (define a7* (fl/ a7 a1))
        (define -a7* (fl* -1.0 a7*))
        (list (flpoly+ (flpoly*s K/S-Q a3*)
                       (flpoly-shift (flpoly*p P/S-Q (flpoly> 1.0 -a7*)) 1))
              a3* a7*)]
       [else ; a1 ≈ 0 => use special form of recurence
        (define -a7 (fl* -1.0 a7))
        (list
         (flpoly+ (flpoly*s K/S-Q a3)
                  (flpoly-shift (flpoly*s P/S-Q -a7) 1))
         a3 a7)])])
  (list K/S-Q a3 a7))

; Compute new estimates of the quadratic coefficients
; using the scalars computed in calcSC
(define (newest [P : flpoly][K : flpoly]
                [tflag : Tflag]
                [a : Flonum][b : Flonum][c : Flonum][d : Flonum][u : Flonum][v : Flonum]
                [a1 : Flonum][a3 : Flonum][a7 : Flonum]
                [f : Flonum][g : Flonum][h : Flonum]) :  (List Flonum Flonum)
  (case tflag
    [(almost-factor)(list 0.0 0.0)]
    [else
     (define-values (a4 a5)
       (case tflag
         [(div-c) (values (fl+ a (fl+ (fl* u b) (fl* h f)))
                          (fl+ c (fl* (fl+ u (fl* v f)) d)))]
         [(div-d) (values (fl+ (fl* (fl+ a g) f) h)
                          (fl+ (fl* (fl+ f u) c) (fl* v d)))]))
  (define b1 (fl* -1.0 (fl/ (flpoly-coefficient K 0)
                            (flpoly-coefficient P 0))))
  (define b2 (fl* -1.0 (fl/ (fl+ (flpoly-coefficient K 1)
                                 (fl* b1 (flpoly-coefficient P 1)))
                            (flpoly-coefficient P 0))))
  (define c1 (fl* v (fl* b2 a1)))
  (define c2 (fl* b1 a7))
  (define c3 (fl* (fl* b1 b1) a3))
  (define c4 (fl- c1 (fl+ c2 c3)))
  (define temp (fl- (fl+ a5 (fl* b1 a4)) c4))
  (if (fl= temp 0.0)
      (list 0.0 0.0)
      (list (fl- u (fl/ (fl+ (fl* u (fl+ c3 c2))
                             (fl* v (fl+ (fl* b1 a1) (fl* b2 a7))))
                        temp))
            (fl* v (fl+ 1.0 (fl/ c4 temp)))))]))

; Variable - shift H - polynomial iteration for a real zero
; sss - starting iterate
; NZ - number of zeros found
; iFlag - flag to indicate a pair of zeros near real axis
(define (RealIT [P : flpoly][K : flpoly]
                [sss : Flonum]) : (List Symbol Flonum)
  (let loop ([i 0]
             [s sss]
             [t 0.0]
             [omp 0.0])
    (define-values (P/S-Q P@s)(flpoly-reduce-root-QR P s))
    ;Compute a rigorous bound on the error in evaluating p
    (define mp (abs P@s))
    (define ms (abs s))
    (define ee (for/fold ([ee : Flonum (fl* 0.5 (abs (flpoly-reverse-coefficient P 0)))])
                         ([i (in-range (- (flpoly-degree P) 1) -1 -1)])
                 (fl+ (fl* ee ms) (abs (flpoly-reverse-coefficient P i)))))
    (cond
      [(<= mp (* 20 epsilon.0 (- (* 2 ee) mp))) (list 'done s)]
      [(< 10 i) (list 'max-iter s)]
      [(and (<= 2 i) (fl<= (abs t) (fl* 0.001 (abs (- s t)))) (< omp mp))
       (list 'zero-cluster s)]
      [else
       (define-values (K/S-Q K@s)(flpoly-reduce-root-QR K s))
       (define K+
         (if (< (fl* epsilon.0 (abs (flpoly-coefficient K 0)))(abs K@s))
             (flpoly+p P/S-Q (flpoly*s K/S-Q (fl* -1.0 (fl/ P@s K@s))));scaled form if K@s is non-zero
             K/S-Q))
       (define K+@s (Horner K+ s))
       (define t (if (< (fl* epsilon.0 (abs (flpoly-coefficient K+ 0)))(abs K+@s))
                     (fl* -1.0 (fl/ P@s K+@s))
                     0.0))
       (loop (+ i 1)
             (+ s t)
             t
             mp)])))

; Variable - shift K - polynomial iteration for a quadratic
; factor converges only if the zeros are equimodular or nearly so.
(define (QuadIT [P : flpoly][K : flpoly]
                [uu : Flonum][vv : Flonum])
  (let loop : (List Symbol (Listof Number))
    ([i : Integer 0]
     [u : Flonum uu][v : Flonum vv]
     [tryFixed? : Boolean #t]
     [relstp : Flonum 0.0]
     [omp : Flonum 0.0])
    (define rts (flpoly-2°root (flpoly> 1.0 u v)))
    ;first focus on the biggest root
    (define-values (sz lz)
      (if (< (real-part (car rts))(real-part (cadr rts)))
          (values (cadr rts)(car rts))
          (values (car rts)(cadr rts))))
    (define szr (fl (real-part sz)))
    (define szi (fl (imag-part sz)))
    (cond
      [(< (* 0.01 (abs (real-part lz))) (abs (- (abs szr)(abs (real-part lz)))))
       ;return if roots of the quadratic are real an not close to multiple or nearly equal and of opposite sign
       (list 'not-ok (list sz))]
      [else
       (define-values (P/S-Q a b)(quadSyntDiv P u v))
       (define mp (fl+ (flabs (fl- a (fl* szr b)))
                       (flabs (fl* szi b))))
       (define zm (flsqrt (flabs v)))
       (define t (fl* -1.0 (fl* szr b)))
       (define ee (for/fold ([ee : Flonum (fl* 2.0 (abs (flpoly-reverse-coefficient P 0)))])
                            ([i (in-range (- (flpoly-degree P) 1) -1 -1)])
                    (fl+ (fl* ee zm) (abs (flpoly-reverse-coefficient P i)))))
       (define ee* (fl+ (fl* ee zm) (flabs (fl+ a t))))
       (define ee** (fl* (fl+ (fl+ (fl* 9.0 ee*) (fl* 2.0 (abs t)))
                              (fl* -7.0 (fl+ (flabs (fl+ a t)) (fl* zm (flabs b)))))
                         epsilon.0))
       (cond
         [(<= mp (* 20 ee**)) (list 'done (list sz lz))]
         [(< 20 i) (list 'max-iter (list sz lz))]
         [else
          (define-values (K* P/S-Q* u* v* a* b* trf?)
            (cond
              [(and tryFixed? (< 2 i)
                    (fl<= relstp 0.01) (fl<= omp mp))
               ;a cluster appears to be stalling the convergence
               ;five fixed shift steps are taken with a u v close to the cluster
               (define relstp* (if (< relstp epsilon.0) (flsqrt epsilon.0) (flsqrt relstp)))
               (define u* (fl- u (fl* u relstp*)))
               (define v* (fl+ v (fl* v relstp*)))
               (define-values (P/S*-Q a* b*)(quadSyntDiv P u* v*))
               (define K*
                 (for/fold : flpoly
                   ([K K])
                   ([i (in-range 5)])
                   (match-define (list tflag K*/S*-Q a1 a3 a7 c d e f g h) (calcSC K u* v* a* b*))
                   (match-define (list K* a3* a7*) (nextK P/S*-Q K*/S*-Q a* b* a1 a3 a7))
                   K*))
               (values K* P/S*-Q u* v* a* b* #f)]
              [else (values K P/S-Q u v a b tryFixed?)]))
          (match-define (list tflag K*/S*-Q (list a1 a3 a7 _ _ _ _ _ _)) (calcSC K* u* v* a* b*))
          (match-define (list K** _ _) (nextK P/S-Q* K*/S*-Q tflag a* b* a1 a3 a7))
          (match-define (list tflag* _ (list a1* a3* a7* c* d* _ f* g* h*)) (calcSC K** u* v* a* b*))
          (match-define (list u** v**) (newest P K** tflag* a* b* c* d* u* v* a1* a3* a7* f* g* h*))
          (cond
            [(fl= 0.0 v**) (list 'not-ok (list sz))]
            [else
             (loop (+ i 1)
                   u** v**
                   trf?
                   (flabs (fl/ (fl- v** v*) v**))
                   mp)])])])))

(define (fixedShift [P : flpoly][K : flpoly]
                    [L2 : Integer]
                    [u : Flonum][v : Flonum]
                    [sr : Flonum])
  (define-values (P/S-Q a b) (quadSyntDiv P u v))
  (let loop ([i : Integer 0]
             [P/S-Q : flpoly P/S-Q]
             [a : Flonum a][b : Flonum b]
             [u : Flonum u][v : Flonum v]
             [calcLst : (List Tflag flpoly (Listof Flonum))(calcSC K u v a b)])
    (match-define (list tflag K/S-Q (list a1 a3 a7 c d e f g h)) calcLst)
    (cond
      [(< L2 i) (list 'max-iter)]
      [else
       ;calculate next K and estimate v
       (match-define (list K* _ _)(nextK P/S-Q K/S-Q tflag a b a1 a3 a7))
       (match-define (list tflag* K*/S-Q a1* a3* a7* c* d* e* f* g* h*)(newest P K* tflag a b c d u v a1 a3 a7 f g h))
       (match-define (list u* v*)(newest P K* tflag* a b c* d* u v a1* a3* a7* f* g* h*))
       (define vv v*)
       ;estimate s
       (define ss (if (= (flpoly-reverse-coefficient K* 0) 0)
                      0.0
                      (fl* -1.0 (fl/ (flpoly-reverse-coefficient P 0)(flpoly-reverse-coefficient K* 0)))))
       (define ts 1.0)
       (define tv 1.0)
       
       1]))
  1)








