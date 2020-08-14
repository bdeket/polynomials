#lang typed/racket/base

(require racket/match)
(require "poly-struct.rkt"
         "root-helper.rkt"
         "root-split.rkt")

(define #:forall (A B)(root-secant [alg : (Algebra (∩ Real A))]
                                   [P : (Poly (∩ Real A B))]
                                   [x_b : (List (∩ Real A) (∩ Real A))]
                                   #:checkΔ [Δfct : (EndFct (∩ Real A))
                                                  (λ ([lst : (Listof (List (∩ Real A) (∩ Real A)))]) : (Option (U 'done 'algorithm-stoped))
                                                    (cond
                                                      [(null? lst) #f]
                                                      [else
                                                       (match-define (list (list x_0 y_0) rst ...) lst)
                                                       (cond
                                                         [(< (abs y_0) 1e-15) 'done]
                                                         [else
                                                          (match-define (list (list x_1 y_1) rst2 ...) rst)
                                                          (cond
                                                            [(< (abs (- x_1 x_0)) 1e-15) 'algorithm-stoped]
                                                            [else #f])])]))]
                                   #:iterations [iterations : Positive-Integer 100]
                                   ) : (iteration-result (∩ Real A))
  (define (Pfct [x : (∩ Real A)]) : (∩ Real A) (poly-evaluate alg P x))
  (define ->t (algebra-->t alg))
  (define t+ (algebra-t+ alg))
  (define t* (algebra-t* alg))
  (define t- (algebra-t- alg))
  (define t/ (algebra-t/ alg))
  (define t0 (algebra-zero alg))
  
  (define (mid [x- : (∩ Real A)][y- : (∩ Real A)]
               [x+ : (∩ Real A)][y+ : (∩ Real A)]): (∩ Real A)
    (t- x- (t* y- (t/ (t- x+ x-)(t- y+ y-)))))
    
  ((inst root-split A B)
   alg P x_b mid Δfct iterations))

(module+ test
  (require "root-helper.rkt")
  (define P1 (make-poly I-algebra '(((2)-1)((0)1))))
  (define R1 ((inst root-secant Exact-Rational Integer)
             Q-algebra P1 (list 0 21/10)))
  (print-iteration-result R1)(newline)
  
  (define P2 (make-poly I-algebra '(((2)1)((0)-1))))
  (define R2 ((inst root-secant Real Integer) R-algebra P2 (list 0 2.1)))
  (print-iteration-result R2)(newline)
  
  (define P3 (make-poly I-algebra '(((2)-1)((0)1))))
  (define R3 ((inst root-secant Real Integer) R-algebra P3 (list 0 10000000000000000000000000)))
  (print-iteration-result R3)(newline)
  
  (define P4 (make-poly I-algebra '(((2)-1)((0)0))))
  (define R4 ((inst root-secant Real Integer) R-algebra P4 (list -101 100)))
  (print-iteration-result R4)(newline))