#lang typed/racket/base

(require racket/match)
(require "poly-struct.rkt"
         "root-helper.rkt")

(provide root-split)

(define #:forall (A B)(root-split [alg : (Algebra+* (∩ Real A))]
                                  [P : (Poly (∩ Real A B))]
                                  [x_b : (List (∩ Real A) (∩ Real A))]
                                  [make-mid : (-> (∩ Real A) (∩ Real A) (∩ Real A) (∩ Real A) (∩ Real A))]
                                  [Δfct : (EndFct (∩ Real A))]
                                  [iterations : Positive-Integer]
                                  ) : (iteration-result (∩ Real A))
  (define (Pfct [x : (∩ Real A)]) : (∩ Real A) (poly-evaluate alg P x))
  (define t* (algebra-t* alg))

  (define (inner [i : Integer]
                 [x- : (∩ Real A)]
                 [y- : (∩ Real A)]
                 [x+ : (∩ Real A)]
                 [y+ : (∩ Real A)]
                 [lst : (Listof (List (∩ Real A) (∩ Real A)))]) : (iteration-result (∩ Real A))
    (define xm (make-mid x- y- x+ y+))
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
  (define lst (list (list x+ y+) (list x- y-)))
  (cond
    [(= 0 y-) (iteration-result x- 'done 0 (reverse lst))]
    [(= 0 y+) (iteration-result x+ 'done 0 lst)]
    [(< (t* y- y+) 0)
     (inner 0
            x- y- x+ y+
            lst)]
    [else
     (error "root-split: Not a bounding interval" lst)]))