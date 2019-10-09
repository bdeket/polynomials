#lang typed/racket/base

(require (only-in math/base float-complex?)
         math/flonum)
(require "poly-mbase.rkt")

(provide (all-defined-out))

(define-type Flonum-Complex (U Float-Complex Flonum))
(define (fl-real [e : Flonum-Complex]) : Flonum (if (float-complex? e) (real-part e) e));<- Why is real-part Float-Complex not Flonum?
(define (fl-imag [e : Flonum-Complex]) : Flonum (if (float-complex? e) (imag-part e) (fl 0)));<- Why is imag-part Float-Complex not Flonum?

(make-poly-base fl Flonum
                fl fl= fl+ fl- fl* fl/ flsum)
(make-poly-realfct fl Flonum
                   flpoly flpoly-v flpoly-degree flpoly*
                   Flonum-Complex fl-real fl-imag make-rectangular
                   fl fl= fl+ fl- fl* fl/
                   flsum flabs)

;------------------------------------------------------------------------------------
;-  extra evaluators
;------------------------------------------------------------------------------------
(define (flHorner+ [P : flpoly][t : Flonum]) : Flonum
  (let loop ([i : Nonnegative-Integer 0]
             [x : Flonum 1.0]
             [ans : (Listof Flonum) '()])
    (cond
      [(< (flpoly-degree P) i) (flsum ans)]
      [else (loop (+ i 1) (* x t) (cons (* x (flpoly-coefficient P i)) ans))])))


(define (hornerEFT [P : flpoly] [t : Flonum]) : (Values Flonum flpoly flpoly)
  (define-values (ans pπ pσ)
    (for/fold : (Values Flonum (Listof Flonum) (Listof Flonum))
      ([ans : Flonum (flpoly-reverse-coefficient P 0)]
       [pπ : (Listof Flonum) '()]
       [pσ : (Listof Flonum) '()])
      ([ai : Flonum ((inst in-vector Flonum) (flpoly-v P) (- (flpoly-degree P) 1) -1 -1)])
      (define-values (pi πi)(fl*/error ans t))
      (define-values (si σi)(fl+/error pi ai))
      (values si (cons πi pπ)(cons σi pσ))))
  (values ans
          (flpolyL< pπ)
          (flpolyL< pσ)))
(define (hornerSum [P1 : flpoly] [P2 : flpoly] [t : Flonum]) : Flonum
  (for/fold ([ans 0.0])
            ([ai ((inst in-vector Flonum) (flpoly-v P1) (flpoly-degree P1) -1 -1)]
             [bi ((inst in-vector Flonum) (flpoly-v P2) (flpoly-degree P2) -1 -1)])
    (fl+ (fl* ans t) (fl+ ai bi))))
(define (compensatedflHorner [P : flpoly][t : Flonum]) : Flonum
  (cond
    [(or (fl= t 0.0)(= (flpoly-degree P) 0))
     (flpoly-coefficient P 0)]
    [else
     (define-values (h pπ pσ)(hornerEFT P t))
     (fl+ h (hornerSum pπ pσ t))]))

;------------------------------------------------------------------------------------
;-  extra product
;------------------------------------------------------------------------------------
;calculates (flpoly*  (flpoly> 1.0 1.0)(flpoly> 1.0 1e-16)(flpoly> 1.0 1e-12)(flpoly> 1.0 1e-13)(flpoly> 1.0 1e-16))
;with less error creep, but around t² times slower than the next algorithm...
(define (flpoly*-accurate [Pf : flpoly]. [Pr : flpoly *]) : flpoly
  (define N (+ (length Pr) 1))
  (define Ps (cons Pf Pr))
  (define d (apply + (map flpoly-degree Ps)))
  (define dm (apply max (map flpoly-degree Ps)))
  (define H : (HashTable (Pair Integer Integer) (Listof Flonum)) (make-hash))
  (define (getcof [Ps : (Listof flpoly)]
                  [n : Positive-Integer]
                  [i : Nonnegative-Integer]) : (Listof Flonum)
    (cond
      [(hash-ref H (cons n i) (λ () #f))]
      [else
       (define n-1 (- n 1))
       (define ans
         (cond
           [(= n-1 0) (list (flpoly-coefficient (car Ps) i))]
           [(< (* dm n) i) '()]
           [else
            (apply
             append
             (for/list : (Listof (Listof Flonum))
               ([j : Nonnegative-Integer (in-range (+ i 1))])
               (define c (flpoly-coefficient (car Ps) (- i j)));<=why can't (- i j) typecheck as Nonnegative-Integer :(
               (if (fl= c 0.0)
                   '()
                   (map (λ ([x : Flonum]) (* c x))
                        (getcof (cdr Ps) n-1 j)))))]));<=why can't (- n 1) typecheck as Nonnegative-Integer :(
       (hash-set! H (cons n i) ans)
       ans]))
  (define v
    (for/vector : (Vectorof Flonum)
      ([i : Nonnegative-Integer (in-range (+ d 1))])
      (flsum (getcof Ps N i))))
  (flpoly v d))


(module+ test
  (flpoly-const (fl 3/8))
  flpoly-zero
  flpoly-one
  (flpoly-copy flpoly-zero)
  (flpolyV< (vector (fl 0) (fl 1) (fl 2) (fl 3/4) (fl 0)))
  (flpoly> (fl 5) (fl 4) (fl 3) (fl 2) (fl 1) (fl 0))

  (flpoly+ (flpoly> (fl 5) (fl 4) (fl 3) (fl 2) (fl 1) (fl 0))
           (flpoly> (fl 0) (fl 1) (fl 2) (fl 3) (fl 4) (fl 5))
           (flpoly> (fl 1) (fl 3) (fl 5) (fl 5) (fl 3) (fl 1)))

  (flpoly* (flpoly> (fl 5) (fl 4) (fl 3) (fl 2) (fl 1) (fl 0))
           (flpoly> (fl 0) (fl 1) (fl 2) (fl 3) (fl 4) (fl 5))
           (flpoly> (fl 1) (fl 3) (fl 5) (fl 5) (fl 3) (fl 1)))

  (flpoly-from-roots  (fl 9998/1000)
                      (fl 9999/1000)
                      (fl 1)
                      (fl 10003/1000)
                      (fl 10003/1000))

  (flpoly-reduce-root-QR (flpoly-from-roots (fl 9998/1000)
                                            (fl 9999/1000)
                                            (fl 1)
                                            (fl 10003/1000)
                                            (fl 10003/1000))
                         1.0)

  (flpoly-reduce-root-QR (flpoly-from-roots (fl 9998/1000)
                                            (fl 9999/1000)
                                            (fl 1)
                                            (fl 10003/1000)
                                            (fl 10003/1000))
                         (fl 9998/1000))

  (flpoly-from-roots (fl 1/2)
                     (make-rectangular (fl 1/3) (fl 1/4))
                     (make-rectangular (fl 1/3) (fl -1/4))))

;------------------------------------
;checking how much improvement the Horner/Horner+/compensatedHorner brings
;anecdotal evidence:
; bigger t (farther from the roots) compensatedHorner wins out
;smaller t (arround roots) Horner+ is the winner (and on average is more accurate than Horner)
;------------------------------------
#;(module+ test
  (require math/bigfloat)
  (define (bfHorner [P : flpoly] [t : Flonum])
    (define T (bf t))
    (for/fold : Bigfloat
      ([sum : Bigfloat (bf 0.0)])
      ([ai ((inst in-vector Flonum) (flpoly-v P) (flpoly-degree P) -1 -1)])
      (bf+ (bf* sum T) (bf ai))))
  ;(define P (flpoly< 1.0 0.0 0.0002 -0.0004 0.0 -1.0))(define a 0.0)(define b 20.0)
  (define P (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))(define a -0.183500)(define b -0.183507)
  
  (define a->b (/ (- b a) 1000.0))
  (define (mfl1 [t : Flonum]) : Flonum (Horner P t))
  (define (mfl2 [t : Flonum]) : Bigfloat (bfHorner P t))
  (define (mfl3 [t : Flonum]) : Flonum (compensatedHorner P t))
  (define (mfl4 [t : Flonum]) : Flonum (Horner+ P t))
  (define (errdiff [t : Flonum])
    (bigfloat->flonum
     (bf-
      (bfabs
       (bf- (mfl2 t)
            (bf (mfl3 t))));error with comp horner
      (bfabs
       (bf- (mfl2 t)
            (bf (mfl1 t))));error with reg horner
      ;if sum is neg -> reg horner error on avarage bigger than comp horner
      )))
  (define (test [t0 : Flonum] [t1 : Flonum] [n : Integer 10000]) : Flonum
    (/
     (for/fold : Flonum
       ([s : Flonum 0.0])
       ([i (in-range n)])
       (define t (+ 0.99 (* 1.01 (random))))
       (fl+ s (errdiff t)))
     n))
  (test .99 1.01)
  (test 0.0 .99)
  (test -4.0 4.0)
  (test -4.0 0.0)
  (test 2.0 6.0)
  (test 2.0 10.0)
  (require plot)
  (plot
   (list
    (function (λ ([T : Real]) (errdiff (fl T))) a b)
    (x-axis)))
  #;(plot
   (list
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl3 (fl t)))));error with comp horner
                 ))
              a b #:color 'blue)
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl1 (fl t)))));error with reg horner
                 ))
              a b)
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl4 (fl t)))));error with horner+
                 ))
              a b #:color 'green)
    (x-axis)))
  (plot
   (list
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl3 (fl t)))));error with comp horner
                     ))) #:size 1 #:color 'blue)
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl1 (fl t)))));error with reg horner
                     ))) #:size 1 #:color 1)
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl4 (fl t)))));error with horner+
                     ))) #:size 1 #:color 'green)
    (x-axis))))
#;(module+ test
  (require plot)
  (define P (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))(define a -0.183500)(define b -0.183507)
  (plot (list (function (λ ([x : Real])(Horner P (fl x))) a b #:color 1)
              (function (λ ([x : Real])(Horner+ P (fl x))) a b #:color 2)
              (function (λ ([x : Real])(compensatedHorner P (fl x))) a b #:color 3))))