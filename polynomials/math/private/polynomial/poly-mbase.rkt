#lang typed/racket/base

(require racket/vector)

(require (for-syntax racket/base
                     racket/syntax))

(provide make-poly-base
         make-poly-realfct
         make-poly-cplxfct)

; real?   precision(e=exact)
;  #t       e       epoly       e
;  #t       fl      flpoly      fl
;  #t       ext     extpoly     ext
;  #t       bf      bfpoly      bf
;  #f       e       ecpoly      ec
;  #f       fl      flcpoly     flc
;  #f       ext     excpoly     exc
;  #f       bf      bfcpoly     bfc


(begin-for-syntax
  (define-syntax with-names
    (syntax-rules ()
      [(with-names id [a ...] body ...)
       (with-syntax ([a (format-id id "~a~a" id (syntax-e #'a))]...)
         body ...)])))
(define-syntax (make-poly-base stx)
  (syntax-case stx ()
    [(_ id TheType
        ->t t=
        t+ t- t* t/
        t-sum)
     (with-names
      #'id [poly poly-v poly-degree poly-size
            poly-const poly-zero poly-one poly-copy
            polyV< polyL< poly< polyV> polyL> poly>
            poly-coefficient poly-reverse-coefficient
            Horner
            poly+p poly+ poly-p poly-
            poly*s poly*p poly*
            poly-shift poly-subst poly-expt
            poly-diff poly-int
            poly/s poly/p-QR poly-reduce-root-QR
            poly->absolute-coefficients]
      #'(begin
          (define t_0 : TheType (->t 0))
          (define t_1 : TheType (->t 1))
          (define t_-1 : TheType (->t -1))
          ;------------------------------------------------------------------------------------
          ;-  constructors
          ;------------------------------------------------------------------------------------
          (struct poly ([v : (Vectorof TheType)][degree : Nonnegative-Integer]) #:transparent)
             
          (define (poly-const [e : TheType]) : poly (poly (vector e) 0))
          (define poly-zero : poly (poly-const t_0))
          (define poly-one : poly (poly-const t_1))
          (define (poly-copy [P : poly]) : poly (poly (vector-copy (poly-v P)) (poly-degree P)))
             
          (define (polyV< [v : (Vectorof TheType)]) : poly
            (define L (vector-length v))
            (cond
              [(equal? v #()) (raise-argument-error 'polyV< "Empty coefficients" v)]
              [else
               (define n : (Option Nonnegative-Integer)
                 (let loop ([i (- L 1)])
                   (cond
                     [(< i 0) #f]
                     [(t= (vector-ref v i) t_0) (loop (- i 1))]
                     [else i])))
               (if n
                   (let ([L* (+ n 1)])(poly (if (= L L*) v (vector-take v L*)) n))
                   poly-zero)]))
          (define (polyL< [a : (Listof TheType)]) : poly (polyV< (list->vector a)))
          (define (poly< [a : TheType] . [b : TheType *]) : poly (polyL< (cons a b)))

          (define (polyV> [v : (Vectorof TheType)]) : poly
            (cond
              [(equal? v #()) (raise-argument-error 'polyV< "Empty coefficients" v)]
              [else
               (define n : (Option Nonnegative-Integer)
                 (for/or ([ai : TheType (in-vector v)]
                          [i : Nonnegative-Integer (in-naturals)])
                   (if (t= ai t_0) #f i)))
               (define d (if n (- (vector-length v) n 1) -1))
               (if (and n (<= 0 d))
                   (poly (for/vector : (Vectorof TheType)
                           ([ai ((inst in-vector TheType) v (- (vector-length v) 1) (- n 1) -1)])
                           ai)
                         d)
                   poly-zero)]))
          (define (polyL> [a : (Listof  TheType)]) : poly (polyV> (list->vector a)))
          (define (poly> [a : TheType] . [b : TheType *]) : poly (polyL> (cons a b)))

          ;------------------------------------------------------------------------------------
          ;-  accessors
          ;------------------------------------------------------------------------------------
          (define (poly-size [P : poly])(vector-length (poly-v P)))
          (define (poly-coefficient [P : poly] [i : Integer]) : TheType
            (cond
              [(<= 0 i (poly-degree P))(vector-ref (poly-v P) i)]
              [else t_0]))
          (define (poly-reverse-coefficient [P : poly] [i : Integer]) : TheType
            (poly-coefficient P (- (poly-degree P) i)))
             
          ;------------------------------------------------------------------------------------
          ;-  evaluator
          ;------------------------------------------------------------------------------------
          (define (Horner [P : poly][t : TheType]) : TheType
            (for/fold : TheType
              ([sum : TheType t_0])
              ([ai ((inst in-vector TheType) (poly-v P) (poly-degree P) -1 -1)])
              (t+ (t* sum t) ai)))

          ;------------------------------------------------------------------------------------
          ;-  sum
          ;------------------------------------------------------------------------------------
          (define (poly+p [P1 : poly] [P2 : poly]) : poly
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (max (poly-degree P1)(poly-degree P2)))])
                        (t+ (poly-coefficient P1 i)(poly-coefficient P2 i))))
            (polyV< v))

          (define (poly+ [Pf : poly] . [Pr : poly *]) : poly
            (define Ps (cons Pf Pr))
            (define d (apply max (map poly-degree Ps)))
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (+ d 1))])
                        (t-sum (map (λ ([P : poly])(poly-coefficient P i)) Ps))))
            (polyV< v))

          ;------------------------------------------------------------------------------------
          ;-  scale
          ;------------------------------------------------------------------------------------
          (define (poly*s [P : poly] [s : TheType]) : poly
            (cond
              [(t= s t_0)(poly-const s)]
              [(t= s t_1)(poly-copy P)]
              [else (poly (for/vector : (Vectorof TheType)
                            ([ai (in-vector (poly-v P))])
                            (t* ai s))
                          (poly-degree P))]))

          ;------------------------------------------------------------------------------------
          ;-  difference
          ;------------------------------------------------------------------------------------
          (define (poly-p [P1 : poly] [P2 : poly]) : poly
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (max (poly-degree P1)(poly-degree P2)))])
                        (t- (poly-coefficient P1 i)(poly-coefficient P2 i))))
            (polyV< v))

          (define (poly- [Pf : poly] . [Pr : poly *])
            (define P- (poly*s Pf t_-1))
            (cond
              [(null? Pr) P-]
              [else (poly*s (apply poly+ P- Pr) t_-1)]))

          ;------------------------------------------------------------------------------------
          ;-  shift
          ;------------------------------------------------------------------------------------
          (define (poly-shift [P : poly] [n : Integer]) : poly
            (define d (poly-degree P))
            (cond
              [(= n 0) (poly-copy P)]
              [(< 0 n) (poly (vector-append (make-vector n t_0) (poly-v P)) (+ d n))]
              [else
               (define d* (+ d n))
               (if (< d* 0)
                   poly-zero
                   (poly (vector-drop (poly-v P) (abs n)) d*))]))

          ;------------------------------------------------------------------------------------
          ;-  product
          ;------------------------------------------------------------------------------------
          (define (poly*p [P1 : poly] [P2 : poly]) : poly
            (define d (+ (poly-degree P1)(poly-degree P2)))
            (define v 
              (for/vector : (Vectorof TheType)
                ([i : Nonnegative-Integer (in-range (+ d 1))])
                (t-sum
                 (for*/list : (Listof TheType)
                   ([k  (in-range (+ i 1))]
                    [l  (in-value (- i k))]);<=why can't this typecheck as Nonnegative-Integer :(
                   (t* (poly-coefficient P1 k)
                       (poly-coefficient P2 l))))))
            (poly v d))
          ;next-one looks nice but is a factor 3 slower :(
          #;(define (poly*p [P1 : poly] [P2 : poly])
              (for/fold ([v poly-zero])
                        ([ai (in-vector (poly-v P1))]
                         [i (in-naturals)])
                (poly+ v (poly*s (poly-shift P2 i) ai))))

          (define (poly* [Pf : poly] . [Pr : poly *]) : poly
            (cond
              [(null? Pr) (poly-copy Pf)]
              [else (apply poly* (poly*p Pf (car Pr)) (cdr Pr))]))


          ;------------------------------------------------------------------------------------
          ;-  substitute variable x for other polynomial
          ;------------------------------------------------------------------------------------
          (define (poly-subst [P : poly] [x : poly]) : poly
            (define-values (sum x^n+1)
              (for/fold
                ([sum : (Listof poly) '()]
                 [x^i-1 : poly poly-one])
                ([i (in-range 1 (poly-size P))])
                (define x^i (poly*p x^i-1 x))
                (values (cons (poly*s x^i (poly-coefficient P i)) sum)
                        x^i)))
            (apply poly+ (poly-const (poly-coefficient P 0)) sum))

          ;------------------------------------------------------------------------------------
          ;-  exponent
          ;------------------------------------------------------------------------------------
          (define (poly-expt [P : poly] [n : Nonnegative-Integer]) : poly
            (cond
              [(= n 0) poly-one]
              [(= n 1) (poly-copy P)]
              [(let ([n/2 (/ n 2)])(if (integer? n/2) n/2 #f))
               =>
               (λ(n/2)(let ([Pi (poly-expt P n/2)])(poly*p Pi Pi)))]
              [else (poly*p P (poly-expt P (- n 1)))]))

          ;------------------------------------------------------------------------------------
          ;-  differentiate
          ;------------------------------------------------------------------------------------
          (define (poly-diff [P : poly] [n : Nonnegative-Integer 1]) : poly
            (define d (poly-degree P))
            (define d* (- d n))
            (cond
              [(< d* 0) poly-zero]
              [(= n 0) (poly-copy P)]
              [else
               (define (inner [V : (Vectorof TheType)] [n : Nonnegative-Integer]) : (Vectorof TheType)
                 (cond
                   [(= n 0) V]
                   [else
                    (inner
                     (for/vector : (Vectorof TheType)
                       ([v (in-vector V 1)]
                        [i (in-naturals 1)])
                       (t* v (->t i)))
                     (- n 1))]))
               (poly (inner (poly-v P) n) d*)]))

          ;------------------------------------------------------------------------------------
          ;-  integrate
          ;------------------------------------------------------------------------------------
          (: poly-int (->* (poly)(Nonnegative-Integer) poly))
          (define (poly-int P [n 1])
            (cond
              [(= n 0) (poly-copy P)]
              [else
               (poly-int
                (poly-shift
                 (poly
                  (for/vector : (Vectorof TheType)
                    ([v (in-vector (poly-v P))]
                     [i (in-naturals 1)])
                    (t/ v (->t i)))
                  (poly-degree P))
                 1)
                (- n 1))]))

          ;------------------------------------
          ;-  division
          ;------------------------------------
          (define (poly/s [P : poly][s : TheType]) : poly
            (poly*s P (t/ t_1 s)))
          
          (define (poly/p-QR [P : poly] [/p : poly]) : (Values poly poly)
            (define dn (poly-degree P))
            (define dd (poly-degree /p))
            (define dQ (- dn dd))
            (cond
              [(< dQ 0) (values poly-zero (poly-copy P))]
              [(= dd 0)
               (values (poly/s P (poly-coefficient /p 0)) poly-zero)]
              [else
               (define R (vector-copy (poly-v P)))
               (define Q (make-vector (+ dQ 1) t_0))
               (for ([k (in-range dQ -1 -1)])
                 (vector-set! Q k (t/ (vector-ref R (+ dd k))
                                      (poly-coefficient /p dd)))
                 (for ([j (in-range (+ dd k -1) (- k 1) -1)])
                   (vector-set! R j (t- (vector-ref R j)
                                        (t* (vector-ref Q k)
                                            (poly-coefficient /p (- j k)))))))
               (values (poly Q dQ)
                       (polyV< (vector-take R dd)))]))

          (define (poly-reduce-root-QR [P : poly] [r : TheType]) : (Values poly TheType)
            (define d (poly-degree P))
            (cond
              [(<= d 0)(values poly-zero (poly-coefficient P 0))]
              [else
               (define v : (Vectorof TheType) (make-vector d t_0))
               (define s
                 (for/fold ([s : TheType (poly-coefficient P d)])
                           ([i (in-range (- d 1) -1 -1)])
                   (vector-set! v i s)
                   (t+ (t* r s) (poly-coefficient P i))))
               (values (poly v (- d 1)) s)]))

         
          ))]))
(define-syntax (make-poly-realfct stx)
  (syntax-case stx ()
    [(_ id TheType
        poly poly-v poly-degree poly*
        TheComplexType tc-real tc-imag make-tc
        ->t t=
        t+ t- t* t/
        t-sum t-abs)
     (with-names
      #'id [poly-from-roots-list poly-from-roots
            poly->absolute-coefficients]
      #'(begin
          (define t_0 : TheType (->t 0))
          (define t_1 : TheType (->t 1))
          (define t_-1 : TheType (->t -1))
          (define (t-real? [t : TheComplexType])(t= t_0 (tc-imag t)))
          ;------------------------------------
          ;-  constructor from roots
          ;------------------------------------
          (define (poly-from-roots-list [rs : (Listof TheComplexType)][s : TheType t_1])
            (define Ss
              (let loop : (Listof poly)([rs : (Listof TheComplexType) rs])
                (cond
                  [(null? rs) '()]
                  [(t-real? (car rs))
                   (cons (poly (vector (t* t_-1 (tc-real (car rs))) t_1) 1)
                         (loop (cdr rs)))]
                  [else
                   (define z (car rs))
                   (define zr (tc-real z))
                   (define zi (tc-imag z))
                   (define z* (make-tc zr (t* t_-1 zi)))
                   (unless (member z* (cdr rs))
                     (raise-argument-error 'poly-from-roots (format "complex conjugate pair (~a ~a)" z z*) z))
                   (cons (poly (vector (t+ (t* zr zr)(t* zi zi)) (t* (->t -2) zr) t_1) 2)
                         (loop (remove z* (cdr rs))))])))
            (apply poly* (poly (vector s) 0) Ss))
          (: poly-from-roots (->* () (#:s TheType) #:rest TheComplexType poly))
          (define (poly-from-roots #:s [s t_1] . rs) (poly-from-roots-list rs s))

          ;------------------------------------
          ;-  absolute coefficient
          ;------------------------------------
          (define (poly->absolute-coefficients [P : poly]) : poly
            (poly (for/vector : (Vectorof TheType)
                    ([v : TheType (in-vector (poly-v P))])(t-abs v))
                         (poly-degree P)))


          ))]))
(define-syntax (make-poly-cplxfct stx)
  (syntax-case stx ()
    [(_ id TheType
        poly poly-v poly-degree poly*
        ->t t=
        t+ t- t* t/
        t-sum)
     (with-names
      #'id [poly-from-roots-list poly-from-roots]
      #'(begin
          (define t_0 : TheType (->t 0))
          (define t_1 : TheType (->t 1))
          (define t_-1 : TheType (->t -1))
          ;------------------------------------
          ;-  constructor from roots
          ;------------------------------------
          (define (poly-from-roots-list [rs : (Listof TheType)][s : TheType t_1])
            (define Ss
              (for/list : (Listof poly)
                ([r (in-list rs)])
                (poly (vector (t* t_-1 r) t_1) 1)))
            (apply poly* (poly (vector s) 0) Ss))
          (: poly-from-roots (->* () (#:s TheType) #:rest TheType poly))
          (define (poly-from-roots #:s [s t_1] . rs)(poly-from-roots-list rs s))


          ))]))
#|
;****************************************************************************************************************************
(module+ epoly
  (provide (except-out (all-defined-out) epoly))
  
  (make-poly-base e Exact-Rational
                  inexact->exact = + - * /
                  (λ ([L : (Listof Exact-Rational)])(apply + L)))
  (make-poly-realfct e Exact-Rational
                     epoly epoly-v epoly-degree epoly*
                     Exact-Number real-part imag-part make-rectangular
                     inexact->exact = + - * /
                     (λ ([L : (Listof Exact-Rational)])(apply + L))
                     abs))

;****************************************************************************************************************************
(module+ flpoly
  (provide (except-out (all-defined-out) flpoly))
  (require math/flonum)
  
  (make-poly-base fl Flonum
                  fl fl= fl+ fl- fl* fl/
                  flsum))


;****************************************************************************************************************************
(module+ extpoly
  (provide (except-out (all-defined-out) extpoly))
  (require racket/extflonum)
  
  (struct extfl-complex ([r : ExtFlonum][i : ExtFlonum]) #:transparent)
  (define-type ExtFlonum-Complex (U ExtFlonum extfl-complex))
  (define (extfl-real-part [e : ExtFlonum-Complex])(if (extflonum? e)  e          (extfl-complex-r e)))
  (define (extfl-imag-part [e : ExtFlonum-Complex])(if (extflonum? e) (->extfl 0) (extfl-complex-i e)))
  
  (make-poly-base ext ExtFlonum
                  real->extfl extfl= extfl+ extfl- extfl* extfl/
                  (λ ([L : (Listof ExtFlonum)])(for/fold : ExtFlonum ([s (->extfl 0)])([l (in-list L)])(extfl+ s l)))))

;****************************************************************************************************************************
(module+ bfpoly
  (provide (except-out (all-defined-out) bfpoly))
  (require math/bigfloat)
  
  (struct bf-complex ([r : Bigfloat][i : Bigfloat]) #:transparent)
  (define-type Bigfloat-Complex (U Bigfloat bf-complex))
  (define (bf-real-part [e : Bigfloat-Complex])(if (bigfloat? e)  e          (bf-complex-r e)))
  (define (bf-imag-part [e : Bigfloat-Complex])(if (bigfloat? e) (bf 0) (bf-complex-i e)))
  (define i.bf (bf-complex (bf 0) (bf 1)))
  
  (make-poly-base bf Bigfloat
                  bf bf= bf+ bf- bf* bf/
                  (λ ([L : (Listof Bigfloat)])(apply bf+ L))))


;****************************************************************************************************************************
(module+ ecpoly
  (define (e* [e1 : Exact-Number][e2 : Exact-Number]) : Exact-Number
    (make-rectangular
     (- (* (real-part e1)(real-part e2))
           (* (imag-part e1)(imag-part e2)))
     (+ (* (imag-part e1)(real-part e2))
           (* (real-part e1)(imag-part e2)))))
  (define (e/ [e1 : Exact-Number][e2 : Exact-Number]) : Exact-Number
    (define d (- (* (real-part e2)(real-part e2))
                 (* (imag-part e2)(imag-part e2))))
    (make-rectangular
     (/ (+ (* (real-part e1)(real-part e2))
           (* (imag-part e1)(imag-part e2)))
        d)
     (/ (- (* (imag-part e1)(real-part e2))
           (* (real-part e1)(imag-part e2)))
        d)))

  (make-poly-base ec Exact-Number
                  inexact->exact = + - e* e/
                  (λ ([L : (Listof Exact-Number)])(apply + L)))
  (make-poly-cplxfct ec Exact-Number
                     ecpoly ecpoly-v ecpoly-degree ecpoly*
                     inexact->exact = + - e* e/
                     (λ ([L : (Listof Exact-Number)])(apply + L)))
  (ecpoly-from-roots 1+i 3 4/2-1/8i))
;****************************************************************************************************************************
(module+ flcpoly
  (require (only-in math/base float-complex?)
           math/flonum)

  (define (flc [a : Number]): Float-Complex (make-rectangular (fl (real-part a))(fl (imag-part a))))
  (define (flcsum [L : (Listof Float-Complex)]) : Float-Complex (flc (apply + L)))
  
  (make-poly-base flc Float-Complex
                  flc = + - * / flcsum)
  (make-poly-cplxfct flc Float-Complex
                     flcpoly flcpoly-v flcpoly-degree flcpoly*
                     flc = + - * / flcsum))
;|#