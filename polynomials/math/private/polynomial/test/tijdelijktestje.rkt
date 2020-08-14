#lang typed/racket/base

(require racket/match)
(require "poly-struct.rkt"
         "root-helper.rkt")

(provide root-split)

(define #:forall (A B)(root-split [alg : (Algebra+* (∩ Real A))]
                                  [P : (Poly (∩ Real A B))]
                                  [x_b : (List (∩ Real A) (∩ Real A))]
                                  [make-mid : (-> (∩ Real A) (∩ Real A) (∩ Real A))]
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
  (define t* (algebra-t* alg))

  (define (inner [i : Integer]
                 [x- : (∩ Real A)]
                 [y- : (∩ Real A)]
                 [x+ : (∩ Real A)]
                 [y+ : (∩ Real A)]
                 [lst : (Listof (List (∩ Real A) (∩ Real A)))]) : (iteration-result (∩ Real A))
    (define xm (make-mid x- x+))
    (define ym (Pfct xm))
    (define lst+ (cons (list xm ym) lst))
    (cond
      [(Δfct lst+) => (λ ([msg : Itermsg])(iteration-result xm msg i lst+))]
      [(<= iterations i) (iteration-result xm 'max-iterations i lst+)]
      [(<= (t* y- ym) 0)
       (inner (+ i 1) x- y- xm ym lst+)]
      [else
       (inner (+ i 1) xm ym x+ y+ lst+)]))

  (define y0 (Pfct (car x_b)))
  (define y1 (Pfct (cadr x_b)))

  (define-values (x- y- x+ y+)
    (if (< y0 y1)
        (values (car x_b) y0 (cadr x_b) y1)
        (values (cadr x_b) y1 (car x_b) y0)))
  (inner 0
         x- y- x+ y+
         (list (list x+ y+) (list x- y-))))