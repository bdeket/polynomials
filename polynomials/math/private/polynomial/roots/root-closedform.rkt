#lang typed/racket/base

(require math/flonum
         (only-in racket/math pi))
(require "../poly-flonum.rkt")

(provide (except-out (prefix-out flpoly- (all-defined-out)) 2π))

(module+ test
  (require typed/rackunit)
  (define (check-roots [A : (Listof Number)]
                       [B : (Listof Number)]
                       [ε : Flonum])
    (define (sortit [A : (Listof Number)])
      ((inst sort Number) A
                          (λ ([a : Number][b : Number])
                            (or (< (- (real-part b) (real-part a)) (- ε))
                                (and (<= (- (real-part b) (real-part a)) ε)
                                     (< (imag-part a)(imag-part b)))))))
    (check-true
     (let loop : Boolean
       ([a (sortit A)]
        [b (sortit B)])
       (cond
         [(and (null? a) (null? b)) #t]
         [(or  (null? a) (null? b)) #f]
;[(begin (println (list (car a) (car b) (magnitude (- (car a) (car b))))) #f)]
         [(< ε (magnitude (- (car a) (car b)))) #f]
         [else (loop (cdr a)(cdr b))]))
     (format "actual: ~a  expected: ~a  precision: ~a" A B ε))))
(define 2π (fl* 2.0 pi))

;------------------------------------
;roots for degree < 4
;------------------------------------
(define (0°root [P : flpoly]) : (Union 'All '())
  (if (fl= (flpoly-coefficient P 0) 0.0)
      'All
      '()))
(module+ test
  (check-equal? (0°root (flpoly> 1.0)) '())
  (check-equal? (0°root (flpoly> 0.0)) 'All))

(define (1°root [P : flpoly]) : (Listof Flonum)
  (list (/ (- (flpoly-coefficient P 0))
           (flpoly-coefficient P 1))))
(module+ test
  (check-roots (1°root (flpoly> 1.0 1.0)) '(-1.0) 1e-16)
  (check-roots (1°root (flpoly> -2.0 0.0)) '(0.0) 1e-16))

(define (2°root [P : flpoly]) : (Listof Number)
  (define a (flpoly-coefficient P 2))
  (define b (flpoly-coefficient P 1))
  (define c (flpoly-coefficient P 0))
  (cond
    [(= b 0)
     (define d1 (fl/ c a))
     (define d (sqrt (flabs d1)))
     (if (fl< 0.0 d1)
         (list (* d -i) (* d +i))
         (list (- d) d))]
  [else
   (define d (* (flsgn b) (sqrt (- (* b b) (* 4 a c)))))
   (define q1 (* -1/2 (+ b d)))
   (define q2 (* -1/2 (- b d)))
   (define q (if (< (magnitude q1) (magnitude q2)) q2 q1))
   (list (/ q a) (/ c q))]))
(module+ test
  (check-roots (2°root (flpoly-from-roots 1.0 2.0)) '(1.0 2.0) 1e-16)
  (check-roots (2°root (flpoly-from-roots 1.9 1e-12)) '(1.9 1e-12) 1e-16)
  (check-roots (2°root (flpoly> 1.0 0.0 1.0)) '(0.0+i 0.0-i) 1e-16)
  (check-roots (2°root (flpoly-from-roots 1e-38 1e-38)) '(1e-38 1e-38) 1e-16))

(define (3°root [P : flpoly]) : (Listof Number)
  (define a (fl/ (flpoly-coefficient P 2)(flpoly-coefficient P 3)))
  (define b (fl/ (flpoly-coefficient P 1)(flpoly-coefficient P 3)))
  (define c (fl/ (flpoly-coefficient P 0)(flpoly-coefficient P 3)))

  (define Q (fl/ (fl+ (fl* a a) (fl* -3.0 b)) 9.0))
  (define R (fl/ (fl+ (fl+ (fl* 2.0 (flexpt a 3.0)) (fl* -9.0 (fl* a b))) (fl* 27.0 c)) 54.0))
  (define R² (flexpt R 2.0))
  (define Q³ (flexpt Q 3.0))
  (cond
    [(and (fl= R² Q³) (fl= R² 0.0)) (define r (fl/ a -3.0))(list r r r)]
    [(fl<= R² Q³)
     (define θ (flacos (fl/ R (flsqrt Q³))))
     (list (fl+ (fl* -2.0 (fl* (flsqrt Q) (flcos (fl/ (fl- θ 2π) 3.0)))) (fl/ a -3.0))
           (fl+ (fl* -2.0 (fl* (flsqrt Q) (flcos (fl/ θ 3.0)))) (fl/ a -3.0))
           (fl+ (fl* -2.0 (fl* (flsqrt Q) (flcos (fl/ (fl+ θ 2π) 3.0)))) (fl/ a -3.0)))]
    [else
     (define A (fl* (fl* -1.0 (flsgn R)) (flexpt (fl+ (flabs R) (flsqrt (fl- R² Q³))) (fl/ 1.0 3.0))))
     (define B (if (fl= A 0.0) 0.0 (fl/ Q A)))
     (define r1 (fl+ (fl+ A B) (fl/ a -3.0)))
     (list r1
           (+ (* -1/2 (+ A B)) (* -1/3 a) (* +i (/ (sqrt 3) 2) (- A B)))
           (+ (* -1/2 (+ A B)) (* -1/3 a) (* -i (/ (sqrt 3) 2) (- A B))))]))
(module+ test
  (check-roots (3°root (flpoly-from-roots 1.0 2.0 3.0)) '(1.0 2.0 3.0) 1e-16)
  (check-roots (3°root (flpoly-from-roots 1.9 1e-12 8.4)) '(1.9 1e-12 8.4) 1e-14)
  (check-roots (3°root (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))
               '(-2.632993161855452 -0.18350341907227397 -0.18350341907227397) 1e-8))
