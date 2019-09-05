#lang typed/racket/base

(require math/flonum
         racket/match)
(require "../poly-flonum.rkt"
         "root-helpers.rkt"
         "root-Newton-flonum.rkt")

(provide (all-defined-out))

;------------------------------------
;bounds
;------------------------------------
(define (abs-coefficient-interval [P : flpoly]) : (List Nonnegative-Flonum Nonnegative-Flonum)
  (define-values (l u)
    (for/fold ([l : Nonnegative-Flonum +inf.0]
               [u : Nonnegative-Flonum 0.0])
              ([v (in-vector (flpoly-v P))])
      (if (= v 0)
          (values l u)
          (values (flmin l (abs v))
                  (flmax u (abs v))))))
  (list l u))
(define (roots-interval [P : flpoly]) : (List Flonum Flonum)
  (define an (flpoly-coefficient P (flpoly-degree P)))
  (define-values (s m)
    (for/fold([s : Flonum  0.0]
              [m : Flonum -1.0])
             ([i (in-range (flpoly-degree P))])
      (define ai (magnitude (fl/ (flpoly-coefficient P i) an)))
      (values (fl+ s ai)(flmax m ai))))
  (define b (flmin (flmax 1.0 s)(fl+ m 1.0)))
  (list (fl* -1.0 b) b))

(define (flpoly-bestscale [P : flpoly]) : Flonum
  (match-define (list sc- sc+) (abs-coefficient-interval P))
  (define sc (fl/ +min.0 (fl* epsilon.0 sc-)))
  (cond
    [(or (and (< sc 1) (<= 10 sc+))
         (and (< 1 sc) (<= sc+ (/ +max.0 sc))))
     (define l (round (fl+ (fl/ (fllog sc)(fllog 2.0)) 0.5)))
     (flexpt 2.0 l)]
    [else 1.0]))

(define (roots-mod-lower-bound [P : flpoly]) : Flonum
  (define pt (flpoly->absolute-coefficients P))
  (vector-set! (flpoly-v pt) 0 (fl* -1.0 (flpoly-coefficient pt 0)))
  (define x0 (flexp (fl/ (fl- (fllog (fl* -1.0 (flpoly-coefficient pt 0)))
                              (fllog (flpoly-coefficient pt (flpoly-degree pt))))
                     (fl (flpoly-degree pt)))))
  (define x1 (if (fl< 0.0 (flpoly-coefficient pt 1))
                 (flmin (fl/ (fl* -1.0 (flpoly-coefficient pt 0))(flpoly-coefficient pt 1)) x0)
                 x0))
  (define dx : Flonum
    (let loop ([x  x1]
               [xm (* 0.1 x1)])
      (if (fl<= (compensatedHorner pt xm) 0.0)
          x
          (loop xm (fl* 0.1 xm)))))
  (define pt* (flpoly-diff pt))
  (define x2 : Flonum
    (let loop ([x dx]
               [dx dx])
      (if (fl<= (flabs (fl/ dx x)) 0.005)
          x
          (let ([δ (fl/ (compensatedHorner pt x)(compensatedHorner pt* x))])(loop (fl- x δ) δ)))))
  x2)
(define (roots-mod-upper-bound [P : flpoly]) : Flonum
  (define pt (flpoly->absolute-coefficients P))
  (vector-set! (flpoly-v pt) (flpoly-degree pt) (fl* -1.0 (flpoly-coefficient pt (flpoly-degree pt))))
  (flresult-root
   (Newton-flroot pt
                  (or (for/or : (Option Flonum)([i (in-naturals)])(if (< 0 (compensatedHorner pt (fl i)))#f(fl i))) 0.0)
                  #:checkΔ (λ ([rts : (Listof (List Flonum Flonum))]) : Boolean
                             (cond
                               [(or (null? rts)(null? (cdr rts))) #f]
                               [else
                                (define x0 (caar rts))(define x1 (caadr rts))
                                (< (abs (/ (- x1 x0) x0)) 0.005)])))))
(define (roots-mod-interval [P : flpoly]) : (List Flonum Flonum)
  (list (roots-mod-lower-bound P)
        (roots-mod-upper-bound P)))


(: make-bracket (-> flpoly (-> Flonum Flonum) (U Flonum (List Flonum Flonum)) (-> Flonum Flonum Flonum Flonum Flonum)
                    (Values Flonum Flonum Flonum Flonum Flonum Flonum)))
(define (make-bracket P Pfct x_0 f)
  (define x-_0 (if (list? x_0) (min (car x_0)(cadr x_0))(car (roots-interval P))))
  (define y-_0 (Pfct x-_0))
  (define x+_0 (if (list? x_0) (max (car x_0)(cadr x_0))(cadr (roots-interval P))))
  (define y+_0 (Pfct x+_0))
  (define xm_0 (if (list? x_0) (fl/ (fl+ x-_0 x+_0) 2.0) x_0))
  (define ym_0 (Pfct xm_0))
  (values x-_0 y-_0 xm_0 ym_0 x+_0 y+_0))
(: make-and-start-bracket
   (case->
    (-> flpoly (-> Flonum Flonum) (U Flonum (List Flonum Flonum)) (-> Flonum Flonum Flonum Flonum Flonum)
        (-> Integer Flonum Flonum Flonum Flonum (Listof (List Flonum Flonum)) (flresult Flonum))
        (flresult Flonum))
    (-> flpoly (-> Flonum Flonum) (U Flonum (List Flonum Flonum)) (-> Flonum Flonum Flonum Flonum Flonum)
        (-> Integer Flonum Flonum Flonum Flonum (Listof (List Flonum Flonum)) (flresult Number))
        (flresult Number))))
(define (make-and-start-bracket P Pfct x_0 f loop)
  (define-values (x-_0 y-_0 xm_0 ym_0 x+_0 y+_0) (make-bracket P Pfct x_0 f))
  (cond
    [(<= (fl* y-_0 ym_0) 0)
     (loop 0 x-_0 y-_0 xm_0 ym_0 (list (list xm_0 ym_0)(list x-_0 y-_0)(list x+_0 y+_0)))]
    [(<= (fl* ym_0 y+_0) 0)
     (loop 0 xm_0 ym_0 x+_0 y+_0 (list (list xm_0 ym_0)(list x+_0 y+_0)(list x-_0 y-_0)))]
    [else ((inst flresult Flonum) xm_0 'invalid-region 0 (list (list xm_0 ym_0)(list x+_0 y+_0)(list x-_0 y-_0)))]))
