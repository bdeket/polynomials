#lang typed/racket/base

(require math/flonum)
(require (for-syntax racket/base
                     racket/syntax))

(require "poly-exact.rkt"
         "poly-exactC.rkt"
         "poly-flonum.rkt"
         "poly-flonumC.rkt")

(provide (except-out (all-defined-out)
                     tower-number tower-poly n->tn p->tn
                     selector make-2poly make-pol+val))

(define (tower-number [a : Number])
  (if (exact? a)
      (if (real? a) 'e 'ec)
      (if (real? a) 'fl 'flc)))
(define (tower-poly [a : poly])
  (if (epoly? a) 'e (if (ecpoly? a) 'ec (if (flpoly? a) 'fl 'flc))))

(: n->tn (case-> (-> Exact-Rational 'e   Exact-Rational)
                 (-> (U Exact-Rational Exact-Number) 'ec  Exact-Number)
                 (-> (U Real Exact-Rational Flonum) 'fl  Flonum)
                 (-> Number         'flc Float-Complex)))
(define (n->tn a tn)
  (case tn
    [(e) a]
    [(ec) a]
    [(fl) (fl a)]
    [(flc) (flc a)]))

(: p->tn (case-> (-> epoly  'e   epoly)
                 (-> (U epoly ecpoly) 'ec  ecpoly)
                 (-> (U epoly flpoly) 'fl  flpoly)
                 (-> poly   'flc flcpoly)))
(define (p->tn P tn)
  (case tn
    [(e) P]
    [(ec) (ecpoly (for/vector : (Vectorof Exact-Number)
                    ([v (poly-v P)])
                    (cast v Exact-Number))
                  (poly-degree P))]
    [(fl) (flpoly (for/vector : (Vectorof Flonum)
                    ([v (poly-v P)])
                    (fl (cast v Real)))
                  (poly-degree P))]
    [(flc) (flcpoly (for/vector : (Vectorof Float-Complex)
                      ([v (poly-v P)])
                      (flc v))
                    (poly-degree P))]))

(define-syntax (selector stx)
  (syntax-case stx ()
    [(_ id P [arg def] ...)
     (with-syntax ([ename (format-id #'id "e~a" (syntax-e #'id))]
                   [ecname (format-id #'id "ec~a" (syntax-e #'id))]
                   [flname (format-id #'id "fl~a" (syntax-e #'id))]
                   [flcname (format-id #'id "flc~a" (syntax-e #'id))])
       #'(define (id P [arg def] ...)
           (cond
             [(epoly? P)  (ename P arg ...)]
             [(ecpoly? P) (ecname P arg ...)]
             [(flpoly? P) (flname P arg ...)]
             [(flcpoly? P)(flcname P arg ...)])))][(_ id P arg ...)
     (with-syntax ([ename (format-id #'id "e~a" (syntax-e #'id))]
                   [ecname (format-id #'id "ec~a" (syntax-e #'id))]
                   [flname (format-id #'id "fl~a" (syntax-e #'id))]
                   [flcname (format-id #'id "flc~a" (syntax-e #'id))])
       #'(define (id P arg ...)
           (cond
             [(epoly? P)  (ename P arg ...)]
             [(ecpoly? P) (ecname P arg ...)]
             [(flpoly? P) (flname P arg ...)]
             [(flcpoly? P)(flcname P arg ...)])))]))
(define-syntax (make-2poly stx)
  (syntax-case stx ()
    [(_ id returntype)
     (with-syntax ([ename (format-id #'id "e~a" (syntax-e #'id))]
                   [ecname (format-id #'id "ec~a" (syntax-e #'id))]
                   [flname (format-id #'id "fl~a" (syntax-e #'id))]
                   [flcname (format-id #'id "flc~a" (syntax-e #'id))])
       #'(define (id [P1 : poly][P2 : poly]) : returntype
           (define ts (list (tower-poly P1) (tower-poly P2)))
           (cond
             [(or (member 'flc ts)
                  (and (member 'fl ts)(member 'ec ts)))
              (flcname (p->tn P1 'flc) (p->tn P1 'flc))]
             [(member 'fl ts)
              (flname (p->tn (cast P1 (U epoly flpoly)) 'fl) (p->tn (cast P2 (U epoly flpoly)) 'fl))]
             [(member 'ec ts)
              (ecname (p->tn (cast P1 (U epoly ecpoly)) 'ec) (p->tn (cast P2 (U epoly ecpoly)) 'ec))]
             [else
              (ename (p->tn (cast P1 epoly) 'e) (p->tn (cast P2 epoly) 'e))])))]))
(define-syntax (make-pol+val stx)
  (syntax-case stx ()
    [(_ id returntype)
     (with-syntax ([ename (format-id #'id "e~a" (syntax-e #'id))]
                   [ecname (format-id #'id "ec~a" (syntax-e #'id))]
                   [flname (format-id #'id "fl~a" (syntax-e #'id))]
                   [flcname (format-id #'id "flc~a" (syntax-e #'id))])
       #'(define (id [P1 : poly][x : Number]) : returntype
           (define ts (list (tower-poly P1) (tower-number x)))
           (cond
             [(or (member 'flc ts)
                  (and (member 'fl ts)(member 'ec ts)))
              (flcname (p->tn P1 'flc) (n->tn x 'flc))]
             [(member 'fl ts)
              (flname (p->tn (cast P1 (U epoly flpoly)) 'fl) (n->tn (cast x Real) 'fl))]
             [(member 'ec ts)
              (ecname (p->tn (cast P1 (U epoly ecpoly)) 'ec) (n->tn (cast x Exact-Number) 'ec))]
             [else
              (ename (p->tn (cast P1 epoly) 'e) (n->tn (cast x Exact-Rational) 'e))])))]))


;------------------------------------------------------------------------------------
;-  Types & accessors
;------------------------------------------------------------------------------------
(define-type poly (U epoly ecpoly flpoly flcpoly))
(define (poly? [a : Any]) : Boolean
  (or (epoly? a)(ecpoly? a)(flpoly? a)(flcpoly? a)))
(define (poly-v [P : poly]) : (Vectorof Number)
  (define V
    (cond
      [(epoly? P)  (epoly-v P)]
      [(ecpoly? P) (ecpoly-v P)]
      [(flpoly? P) (flpoly-v P)]
      [(flcpoly? P)(flcpoly-v P)]));<=Why can't this just be (Vectorof Number)
  (for/vector : (Vectorof Number)([v V])v))


(: poly-degree (-> poly Nonnegative-Integer))
(selector poly-degree P)
(: poly-size (-> poly Nonnegative-Integer))
(selector poly-size P)
(: poly-coefficient (-> poly Integer Number))
(selector poly-coefficient P i)
(: poly-reverse-coefficient (-> poly Integer Number))
(selector poly-reverse-coefficient P i)

;------------------------------------------------------------------------------------
;-  Constructors
;------------------------------------------------------------------------------------
(define (vector/ascending->poly [V : (Vectorof Number)]) : poly
  (define ts (for/list : (Listof (U 'e 'ec 'fl 'flc)) ([v V])(tower-number v)))
  (cond
    [(or (member 'flc ts)
         (and (member 'fl ts)(member 'ec ts)))
     (flcvector/ascending->poly (for/vector : (Vectorof Float-Complex) ([v V])(flc v)))]
    [(member 'fl ts)
     (flvector/ascending->poly (for/vector : (Vectorof Flonum) ([v (cast V (Vectorof Real))])(fl v)))]
    [(member 'ec ts)
     (ecvector/ascending->poly (cast V (Vectorof Exact-Number)))]
    [else
     (evector/ascending->poly (cast V (Vectorof Exact-Rational)))]))
(define (list/ascending->poly [L : (Listof Number)]) : poly (vector/ascending->poly (list->vector L)))
(define (poly/ascending [a0 : Number] . [ar : Number *]) : poly (list/ascending->poly (cons a0 ar)))
(define (vector/descending->poly [V : (Vectorof Number)]) : poly (list/descending->poly (vector->list V)))
(define (list/descending->poly [L : (Listof Number)]) : poly (vector/ascending->poly (list->vector (reverse L))))
(define (poly/descending [a0 : Number] . [ar : Number *]) : poly (list/descending->poly (cons a0 ar)))
(define (poly-constant [a : Number]) : poly (vector/ascending->poly (vector a)))

(define poly-zero : poly epoly-zero)
(define poly-one  : poly  epoly-one)

(: poly-copy (-> poly poly))
(selector poly-copy P)
(: poly->absolute-coefficients (-> poly poly))
(selector poly->absolute-coefficients P)

(define (poly-from-roots-list [rs : (Listof Number)][s : Number 1])
  (define ts (for/list : (Listof (U 'e 'ec 'fl 'flc)) ([v (cons s rs)])(tower-number v)))
  (cond
    [(or (member 'flc ts)
         (and (member 'fl ts)(member 'ec ts)))
     (flcpoly-from-roots-list (map flc rs)(flc s))]
    [(member 'fl ts)
     (flpoly-from-roots-list (map fl (cast rs (Listof Real)))(fl (cast s Real)))]
    [(member 'ec ts)
     (ecpoly-from-roots-list (cast rs (Listof Exact-Number))(cast s Exact-Number))]
    [else
     (epoly-from-roots-list (cast rs (Listof Exact-Rational))(cast s Exact-Rational))]))
(: poly-from-roots (->* () (#:s Number) #:rest Number poly))
(define (poly-from-roots #:s [s 1] . rs) : poly (poly-from-roots-list rs s))

;------------------------------------------------------------------------------------
;-  Evaluators
;------------------------------------------------------------------------------------
(make-pol+val poly-eval Number)
;------------------------------------------------------------------------------------
;-  Basic operations
;------------------------------------------------------------------------------------
(: poly-expt (-> poly Nonnegative-Integer poly))
(selector poly-expt P i)

(make-pol+val poly*s poly)
(make-pol+val poly/s poly)
(make-pol+val poly-scale poly)

(make-2poly poly+p poly)
(define (poly+ [P1 : poly] . [P2 : poly *])
  (for/fold ([sum : poly P1])
            ([P (in-list P2)])
    (poly+p sum P)))

(make-2poly poly-p poly)
(define (poly- [P1 : poly] . [P2 : poly *])
  (cond
    [(null? P2) (poly*s P1 -1)]
    [else
     (for/fold ([sum : poly P1])
               ([P (in-list P2)])
       (poly-p sum P))]))

(make-2poly poly*p poly)
(define (poly* [P1 : poly] . [P2 : poly *])
  (for/fold ([sum : poly P1])
            ([P (in-list P2)])
    (poly*p sum P)))

(make-2poly poly/p-QR (Values poly poly))
(make-pol+val poly-reduce-root-QR (Values poly Number))

(make-2poly poly-substitute poly)

(: poly-shift (-> poly Integer poly))
(selector poly-shift P i)
(: poly-diff (->* (poly) (Nonnegative-Integer) poly))
(selector poly-diff P [i 1])
(: poly-int (->* (poly) (Nonnegative-Integer) poly))
(selector poly-int P [i 1])
(: poly->coefficients-list (-> poly (Listof (List (List Nonnegative-Integer) Number))))
(selector poly->coefficients-list P)
