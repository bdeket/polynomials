#lang typed/racket/base

(require math/flonum
         racket/match)
(require "../poly-flonum.rkt")

(provide (all-defined-out))

(define-type cPevaluator (case-> (-> flpoly Flonum Flonum)
                                 (-> flpoly Number Number)));<=why can't this be (flpoly Number Float-Complex) (error for the flonum? case)
(: fl/cHorner cPevaluator)
(define (fl/cHorner p x)
  (local-require (only-in "../poly.rkt" Horner))
  (cond
    [(flonum? x) (flHorner p x)]
    [else (Horner p x)]))
(define (fl/c [n : Number])
  (local-require (only-in "../poly-flonumC.rkt" flc))
  (if (real? n) (fl n) (flc n)))

;------------------------------------
;iterative-root result
;------------------------------------
(define-type Itermsg (U 'done 'max-iterations 'local-extremum 'invalid-region 'algorithm-stoped))
(struct (A) flresult ([root : A][endmsg : Itermsg][iterations : Integer][iteration-values : (Listof (List A A))]))

;------------------------------------
;stopping conditions
;------------------------------------
(define-type flEndFct (-> (Listof (List Flonum Flonum)) Boolean))
(define-type EndFct (-> (Listof (List Number Number)) Boolean))

(: flendfct flEndFct)
(define (flendfct rts)
  (cond
    [(null? rts) #f]
    [else
     (define x_k (caar rts))
     (define y_k (cadar rts))
     (cond
       [(< (flabs y_k) (flulp x_k)) #t]
       [(null? (cdr rts)) #f]
       [else
        (define Δ_k (- (caadr rts) x_k))
        (<= (flabs Δ_k) (flulp x_k))])]))

(: endfct EndFct)
(define (endfct rts)
  (cond
    [(null? rts) #f]
    [else
     (define x_k (caar rts))
     (define y_k (cadar rts))
     (define fmx (flulp (fl (magnitude x_k))))
     (cond
       [(< (magnitude y_k) fmx) #t]
       [(null? (cdr rts)) #f]
       [else
        (define Δ_k (- (caadr rts) x_k))
        (<= (magnitude Δ_k) fmx)])]))

; Nikolajsen, Jorgen L. "New stopping criteria for iterative root finding."  Royal Society open science (2014)
(: Ward-endfct EndFct)
(define (Ward-endfct rts)
  (cond
    [(or (null? rts)(null? (cdr rts))(null? (cddr rts))) #f]
    [else
     (define y0 (cadr (car rts)))
     (define y1 (cadr (cadr rts)))
     (define y2 (cadr (caddr rts)))
     (define y1m (magnitude y1))
     (define e0 (magnitude (- y0 y1)))
     (define e1 (magnitude (- y1 y2)))
     (and (< e0 e1)
         (if (< y1m 1e-8)
             (< e0 1e-14)
             (<= (/ e0 y1m) 1e-10)))]))

;------------------------------------
;better-interval
;------------------------------------
(define (inspect-iterations [rslt : (flresult Number)]) : (Listof (List Flonum Flonum))
  (define lst+1
    (let loop : (Listof (List Flonum Flonum))
      ([l : (Listof (List Number Number)) (flresult-iteration-values rslt)])
      (cond
        [(null? l) '()]
        [(and (flonum? (caar l))(flonum? (cadar l)))
         (cons (car l)(loop (cdr l)))]
        [else (loop (cdr l))])))
  (cond
    [(or (null? lst+1)(null? (cdr lst+1))) '()]
    [else
     (define lst+2
       ((inst sort (List Flonum Flonum)) lst+1 < #:key car))

     (for/list : (Listof (List Flonum Flonum))
         ([l1 : (List Flonum Flonum) (in-list lst+2)]
          [l2 : (List Flonum Flonum) (in-list lst+2)]
          #:when (fl< (fl* (cadr l1)(cadr l2)) 0.0))
       (list (car l1)(car l2)))]))
