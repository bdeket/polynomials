#lang typed/racket/base

(require racket/vector)

(require (for-syntax typed/racket/base
                     racket/syntax
                     syntax/parse))

(provide make-poly-base
         make-poly-base+int/diff
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

;(struct (A) poly ([v : (Vectorof A)][degree : Nonnegative-Integer]) #:transparent)


(define-syntax-rule (typecheck x type)(begin (: check type)(define check x)))
(begin-for-syntax
  (define-syntax with-names
    (syntax-rules ()
      [(with-names id [a ...] body ...)
       (with-syntax ([a (format-id id "~a~a" id (syntax-e #'a))]...)
         body ...)])))
(define-syntax (make-poly-base stx)
  (syntax-parse stx
    [(_ [name:id (~literal :) TheType:expr]
        ->o:expr
        o+:expr o-:expr o*:expr o/:expr
        (~optional (~seq #:= o=:expr) #:defaults ([o= #'equal?]))
        (~optional (~seq #:sum o-sum:expr)))
     (with-names
      #'name [poly poly-make poly? poly-v poly-degree poly-size Poly
              poly-constant poly-zero poly-one poly-copy
              vector/ascending->poly list/ascending->poly poly/ascending
              vector/descending->poly list/descending->poly poly/descending
              poly-coefficient poly-reverse-coefficient poly->coefficients-list
              poly-eval
              poly+p poly+ poly-p poly-
              poly-scale poly*s poly/s
              poly*p poly*
              poly-shift poly-substitute poly-expt
              poly/p-QR poly-reduce-root-QR
              poly->absolute-coefficients]
     #'(begin
          ;------------------------------------------------------------------------------------
          ;-  copy external functions to shift TypeError blame
          ;------------------------------------------------------------------------------------
          (: ->t (-> Integer TheType))       (define ->t ->o)
          (: t+ (-> TheType TheType TheType))(define t+ o+)
          (: t- (-> TheType TheType TheType))(define t- o-)
          (: t* (-> TheType TheType TheType))(define t* o*)
          (: t/ (-> TheType TheType TheType))(define t/ o*)
          (: t= (-> TheType TheType Boolean))(define t= o=)

         (define t_0 : TheType (->t 0))
         (define t_1 : TheType (->t 1))
         (define t_-1 : TheType (t- t_0 t_1))
         (: t-sum (-> (Listof TheType) TheType))
         (define t-sum (~? (~@ o-sum)
                           (~@ (λ ([lst : (Listof TheType)]) : TheType
                                 (for/fold ([s : TheType t_0])
                                           ([l (in-list lst)])
                                   (t+ s l))))))
          ;------------------------------------------------------------------------------------
          ;-  constructors
          ;------------------------------------------------------------------------------------
          (struct poly ([v : (Vectorof TheType)][degree : Nonnegative-Integer]) #:transparent #:constructor-name poly-make)
          (define-type Poly poly)
             
          (define (poly-constant [e : TheType]) : Poly (poly-make (vector e) 0))
          (define poly-zero : Poly (poly-constant t_0))
          (define poly-one : Poly (poly-constant t_1))
          (define (poly-copy [P : Poly]) : Poly (poly-make (vector-copy (poly-v P)) (poly-degree P)))
             
          (define (vector/ascending->poly [v : (Vectorof TheType)]) : Poly
            (define L (vector-length v))
            (cond
              [(equal? v #()) (raise-argument-error 'vector/ascending->poly "Empty coefficients" v)]
              [else
               (define n : (Option Nonnegative-Integer)
                 (let loop ([i (- L 1)])
                   (cond
                     [(< i 0) #f]
                     [(t= (vector-ref v i) t_0) (loop (- i 1))]
                     [else i])))
               (if n
                   (let ([L* (+ n 1)])(poly-make(if (= L L*) v (vector-take v L*)) n))
                   poly-zero)]))
          (define (list/ascending->poly [a : (Listof TheType)]) : Poly (vector/ascending->poly (list->vector a)))
          (define (poly/ascending [a : TheType] . [b : TheType *]) : Poly (list/ascending->poly (cons a b)))

          (define (vector/descending->poly [v : (Vectorof TheType)]) : Poly
            (cond
              [(equal? v #()) (raise-argument-error 'vector/ascending->poly "Empty coefficients" v)]
              [else
               (define n : (Option Nonnegative-Integer)
                 (for/or ([ai : TheType (in-vector v)]
                          [i : Nonnegative-Integer (in-naturals)])
                   (if (t= ai t_0) #f i)))
               (define d (if n (- (vector-length v) n 1) -1))
               (if (and n (<= 0 d))
                   (poly-make(for/vector : (Vectorof TheType)
                           ([ai ((inst in-vector TheType) v (- (vector-length v) 1) (- n 1) -1)])
                           ai)
                         d)
                   poly-zero)]))
          (define (list/descending->poly [a : (Listof  TheType)]) : Poly (vector/descending->poly (list->vector a)))
          (define (poly/descending [a : TheType] . [b : TheType *]) : Poly (list/descending->poly (cons a b)))

          ;------------------------------------------------------------------------------------
          ;-  accessors
          ;------------------------------------------------------------------------------------
          (define (poly-size [P : Poly])(vector-length (poly-v P)))
          (define (poly-coefficient [P : Poly] [i : Integer]) : TheType
            (cond
              [(<= 0 i (poly-degree P))(vector-ref (poly-v P) i)]
              [else t_0]))
          (define (poly-reverse-coefficient [P : Poly] [i : Integer]) : TheType
            (poly-coefficient P (- (poly-degree P) i)))

          (define (poly->coefficients-list [P : Poly]) : (Listof (List (List Nonnegative-Integer) TheType))
            (if (= (poly-degree P) 0)(list (list '(0) (poly-coefficient P 0)))
                (for/list ([v (in-vector (poly-v P))]
                           [i : Nonnegative-Integer (in-naturals)]
                           #:unless (t= t_0 v))
                  (list (list i) v))))
             
          ;------------------------------------------------------------------------------------
          ;-  evaluator
          ;------------------------------------------------------------------------------------
          (define (poly-eval [P : Poly][t : TheType]) : TheType
            (for/fold : TheType
              ([sum : TheType t_0])
              ([ai ((inst in-vector TheType) (poly-v P) (poly-degree P) -1 -1)])
              (t+ (t* sum t) ai)))

          ;------------------------------------------------------------------------------------
          ;-  sum
          ;------------------------------------------------------------------------------------
          (define (poly+p [P1 : Poly] [P2 : Poly]) : Poly
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (max (poly-degree P1)(poly-degree P2)))])
                        (t+ (poly-coefficient P1 i)(poly-coefficient P2 i))))
            (vector/ascending->poly v))

          (define (poly+ [Pf : (U poly TheType)] . [Pr : (U poly TheType) *]) : Poly
            (define Ps (map (λ ([x : (U poly TheType)]) (if (poly? x) x (poly-constant x)))(cons Pf Pr)))
            (define d (apply max (map poly-degree Ps)))
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (+ d 1))])
                        (t-sum (map (λ ([P : Poly])(poly-coefficient P i)) Ps))))
            (vector/ascending->poly v))

          ;------------------------------------------------------------------------------------
          ;-  scale
          ;------------------------------------------------------------------------------------
          (define (poly*s [P : Poly] [s : TheType]) : Poly
            (cond
              [(t= s t_0)(poly-constant s)]
              [(t= s t_1)(poly-copy P)]
              [else (poly-make(for/vector : (Vectorof TheType)
                            ([ai (in-vector (poly-v P))])
                            (t* ai s))
                          (poly-degree P))]))
          (define poly-scale poly*s)

          ;------------------------------------------------------------------------------------
          ;-  difference
          ;------------------------------------------------------------------------------------
          (define (poly-p [P1 : Poly] [P2 : Poly]) : Poly
            (define v (for/vector : (Vectorof TheType)
                        ([i (in-range (max (poly-degree P1)(poly-degree P2)))])
                        (t- (poly-coefficient P1 i)(poly-coefficient P2 i))))
            (vector/ascending->poly v))

          (define (poly- [Pf : (U poly TheType)] . [Pr : (U poly TheType) *]) : Poly
            (define P- (poly*s (if (poly? Pf) Pf (poly-constant Pf)) t_-1))
            (cond
              [(null? Pr) P-]
              [else (poly*s (apply poly+ P- Pr) t_-1)]))

          ;------------------------------------------------------------------------------------
          ;-  shift
          ;------------------------------------------------------------------------------------
          (define (poly-shift [P : Poly] [n : Integer]) : Poly
            (define d (poly-degree P))
            (cond
              [(= n 0) (poly-copy P)]
              [(< 0 n) (poly-make (vector-append (make-vector n t_0) (poly-v P)) (+ d n))]
              [else
               (define d* (+ d n))
               (if (< d* 0)
                   poly-zero
                   (poly-make (vector-drop (poly-v P) (abs n)) d*))]))

          ;------------------------------------------------------------------------------------
          ;-  product
          ;------------------------------------------------------------------------------------
          (define (poly*p [P1 : Poly] [P2 : Poly]) : Poly
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
            (poly-make v d))
          ;next-one looks nice but is a factor 3 slower :(
          #;(define (poly*p [P1 : Poly] [P2 : Poly])
              (for/fold ([v poly-zero])
                        ([ai (in-vector (poly-v P1))]
                         [i (in-naturals)])
                (poly+ v (poly*s (poly-shift P2 i) ai))))

          (define (poly* [Pf : (U poly TheType)] . [Pr : (U poly TheType) *]) : Poly
            (define (inner [Pf : Poly][Pr : (Listof (U poly TheType))]) : Poly
              (cond
                [(null? Pr) Pf]
                [(poly? (car Pr))(inner (poly*p Pf (car Pr)) (cdr Pr))]
                [else (inner (poly*s Pf (car Pr)) (cdr Pr))]))
            (cond
              [(not (poly? Pf)) (inner (poly-constant Pf) Pr)]
              [(null? Pr) (poly-copy Pf)]
              [else (inner Pf Pr)]))


          ;------------------------------------------------------------------------------------
          ;-  substitute variable x for other polynomial
          ;------------------------------------------------------------------------------------
          (define (poly-substitute [P : Poly] [x : Poly]) : Poly
            (define-values (sum x^n+1)
              (for/fold
                ([sum : (Listof poly) '()]
                 [x^i-1 : Poly poly-one])
                ([i (in-range 1 (poly-size P))])
                (define x^i (poly*p x^i-1 x))
                (values (cons (poly*s x^i (poly-coefficient P i)) sum)
                        x^i)))
            (apply poly+ (poly-constant (poly-coefficient P 0)) sum))

          ;------------------------------------------------------------------------------------
          ;-  exponent
          ;------------------------------------------------------------------------------------
          (define (poly-expt [P : Poly] [n : Nonnegative-Integer]) : Poly
            (cond
              [(= n 0) poly-one]
              [(= n 1) (poly-copy P)]
              [(let ([n/2 (/ n 2)])(if (integer? n/2) n/2 #f))
               =>
               (λ(n/2)(let ([Pi (poly-expt P n/2)])(poly*p Pi Pi)))]
              [else (poly*p P (poly-expt P (- n 1)))]))

          ;------------------------------------
          ;-  division
          ;------------------------------------
          (define (poly/s [P : Poly][s : TheType]) : Poly
            (poly*s P (t/ t_1 s)))
          
          (define (poly/p-QR [P : Poly] [/p : Poly]) : (Values poly poly)
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
               (values (poly-make Q dQ)
                       (vector/ascending->poly (vector-take R dd)))]))

          (define (poly-reduce-root-QR [P : Poly] [r : TheType]) : (Values poly TheType)
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
               (values (poly-make v (- d 1)) s)]))

          ))]))
(define-syntax (make-poly-base+int/diff stx)
  (syntax-parse stx
    [(_ [name:id (~literal :) TheType:expr]
        ->o:expr 
        o+:expr o-:expr o*:expr o/:expr
        (~optional (~seq #:= o=:expr))
        (~optional (~seq #:sum o-sum:expr)))
     (with-names
      #'name [poly-int poly-diff
              ;provided by base:
              Poly poly-make poly-degree poly-zero poly-copy poly poly-v poly-shift]
      #'(begin
          ;------------------------------------------------------------------------------------
          ;-  copy external functions to shift TypeError blame
          ;------------------------------------------------------------------------------------
          (: ->t (-> Integer TheType))(define ->t ->o)
          (: t* (-> TheType TheType TheType))(define t* o*)
          (: t/ (-> TheType TheType TheType))(define t/ o*)
          ;------------------------------------------------------------------------------------
          ;-  load base
          ;------------------------------------------------------------------------------------
          (make-poly-base [name : TheType]
                          ->t o+ o- t* t/
                          (~? (~@ #:= o=))
                          (~? (~@ #:sum o-sum)))
          ;------------------------------------------------------------------------------------
          ;-  differentiate
          ;------------------------------------------------------------------------------------
          (define (poly-diff [P : Poly] [n : Nonnegative-Integer 1]) : Poly
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
               (poly-make (inner (poly-v P) n) d*)]))

          ;------------------------------------------------------------------------------------
          ;-  integrate
          ;------------------------------------------------------------------------------------
          (: poly-int (->* (Poly)(Nonnegative-Integer) Poly))
          (define (poly-int P [n 1])
            (cond
              [(= n 0) (poly-copy P)]
              [else
               (poly-int
                (poly-shift
                 (poly-make
                  (for/vector : (Vectorof TheType)
                    ([v (in-vector (poly-v P))]
                     [i (in-naturals 1)])
                    (t/ v (->t i)))
                  (poly-degree P))
                 1)
                (- n 1))]))))]))


(define-syntax (make-poly-realfct stx)
  (syntax-parse stx
    [(_ [name:id (~literal :) TheType:expr]
        [make-tc:expr (~literal :) TheComplexType:expr] tc-real:expr tc-imag:expr
        ->o:expr o+:expr o-:expr o*:expr o/:expr o-abs:expr
        (~optional (~seq #:= o=:expr) #:defaults ([o= #'equal?]))
        (~optional (~seq #:sum o-sum:expr)))
     (with-names
      #'name [poly-from-roots-list poly-from-roots
              poly->absolute-coefficients
              ;provided by base:
              Poly poly-make poly-v poly-degree poly*]
      #'(begin
          ;------------------------------------------------------------------------------------
          ;-  copy external functions to shift TypeError blame
          ;------------------------------------------------------------------------------------
          (: ->t (-> Integer TheType))       (define ->t ->o)
          (: t+ (-> TheType TheType TheType))(define t+ o+)
          (: t- (-> TheType TheType TheType))(define t- o-)
          (: t* (-> TheType TheType TheType))(define t* o*)
          (: t= (-> TheType TheType Boolean))(define t= o=)
          (: t-abs (-> TheType TheType))(define t-abs o-abs)
          (define t_0 : TheType (->t 0))
          (define t_1 : TheType (->t 1))
          (define t_-1 : TheType (t- t_0 t_1))
          (define t_-2 : TheType (t+ t_-1 t_-1))
          (define (t-real? [t : TheComplexType])(t= t_0 (tc-imag t)))
          ;------------------------------------------------------------------------------------
          ;-  load base
          ;------------------------------------------------------------------------------------
          (make-poly-base+int/diff [name : TheType]
                                   ->t t+ t- t* o/
                                   #:= t=
                                   (~? (~@ #:sum o-sum)))
          ;------------------------------------
          ;-  constructor from roots
          ;------------------------------------
          (define (poly-from-roots-list [rs : (Listof TheComplexType)][s : TheType t_1])
            (define Ss
              (let loop : (Listof Poly)([rs : (Listof TheComplexType) rs])
                (cond
                  [(null? rs) '()]
                  [(t-real? (car rs))
                   (cons (poly-make (vector (t* t_-1 (tc-real (car rs))) t_1) 1)
                         (loop (cdr rs)))]
                  [else
                   (define z (car rs))
                   (define zr (tc-real z))
                   (define zi (tc-imag z))
                   (define z* (make-tc zr (t* t_-1 zi)))
                   (unless (member z* (cdr rs))
                     (raise-argument-error 'poly-from-roots (format "complex conjugate pair (~a ~a)" z z*) z))
                   (cons (poly-make (vector (t+ (t* zr zr)(t* zi zi)) (t* t_-2 zr) t_1) 2)
                         (loop (remove z* (cdr rs))))])))
            (apply poly* (poly-make (vector s) 0) Ss))
          (: poly-from-roots (->* () (#:s TheType) #:rest TheComplexType Poly))
          (define (poly-from-roots #:s [s t_1] . rs) (poly-from-roots-list rs s))

          ;------------------------------------
          ;-  absolute coefficient
          ;------------------------------------
          (define (poly->absolute-coefficients [P : Poly]) : Poly
            (poly-make (for/vector : (Vectorof TheType)
                    ([v : TheType (in-vector (poly-v P))])(t-abs v))
                         (poly-degree P)))


          ))]))
(define-syntax (make-poly-cplxfct stx)
  (syntax-parse stx
    [(_ [name:id (~literal :) TheType:expr]
        ->o:expr o+:expr o-:expr o*:expr o/:expr
        (~optional (~seq #:= o=:expr) #:defaults ([o= #'equal?]))
        (~optional (~seq #:sum o-sum:expr)))
     (with-names
      #'name [poly-from-roots-list poly-from-roots
              ;provided by base
              Poly poly-make poly-v poly-degree poly*]
      #'(begin
          ;------------------------------------------------------------------------------------
          ;-  copy external functions to shift TypeError blame
          ;------------------------------------------------------------------------------------
          (: ->t (-> Integer TheType))       (define ->t ->o)
          (: t- (-> TheType TheType TheType))(define t- o-)
          (: t* (-> TheType TheType TheType))(define t* o*)
          (define t_0 : TheType (->t 0))
          (define t_1 : TheType (->t 1))
          (define t_-1 : TheType (t- t_0 t_1))
          ;------------------------------------------------------------------------------------
          ;-  load base
          ;------------------------------------------------------------------------------------
          (make-poly-base+int/diff [name : TheType]
                                   ->t o+ t- t* o/
                                   (~? (~@ #:= o=))
                                   (~? (~@ #:sum o-sum)))
          ;------------------------------------
          ;-  constructor from roots
          ;------------------------------------
          (define (poly-from-roots-list [rs : (Listof TheType)][s : TheType t_1])
            (define Ss
              (for/list : (Listof Poly)
                ([r (in-list rs)])
                (poly-make (vector (t* t_-1 r) t_1) 1)))
            (apply poly* (poly-make (vector s) 0) Ss))
          (: poly-from-roots (->* () (#:s TheType) #:rest TheType Poly))
          (define (poly-from-roots #:s [s t_1] . rs)(poly-from-roots-list rs s))


          ))]))
;****************************************************************************************************************************
#;(module+ epoly
  (provide (except-out (all-defined-out) epoly))
  
  (make-poly-realfct [e : Exact-Rational]
                     [make-rectangular : Exact-Number] real-part imag-part 
                     values + - * / abs #:= =))

;****************************************************************************************************************************
#;(module+ flpoly
  (provide (except-out (all-defined-out) flpoly))
  (require math/flonum)
  
  (make-poly-base [fl : Flonum]
                  fl fl+ fl- fl* fl/
                  #:= fl=
                  #:sum flsum))


;****************************************************************************************************************************
#;(module+ extpoly
  (provide (except-out (all-defined-out) extpoly))
  (require racket/extflonum)
  
  (struct extfl-complex ([r : ExtFlonum][i : ExtFlonum]) #:transparent)
  (define-type ExtFlonum-Complex (U ExtFlonum extfl-complex))
  (define (extfl-real-part [e : ExtFlonum-Complex])(if (extflonum? e)  e          (extfl-complex-r e)))
  (define (extfl-imag-part [e : ExtFlonum-Complex])(if (extflonum? e) (->extfl 0) (extfl-complex-i e)))
  
  (make-poly-base [ext : ExtFlonum]
                  real->extfl extfl+ extfl- extfl* extfl/
                  #:= extfl=))

;****************************************************************************************************************************
#;(module+ bfpoly
  (provide (except-out (all-defined-out) bfpoly))
  (require math/bigfloat)
  
  (struct bf-complex ([r : Bigfloat][i : Bigfloat]) #:transparent)
  (define-type Bigfloat-Complex (U Bigfloat bf-complex))
  (define (bf-real-part [e : Bigfloat-Complex])(if (bigfloat? e)  e          (bf-complex-r e)))
  (define (bf-imag-part [e : Bigfloat-Complex])(if (bigfloat? e) (bf 0) (bf-complex-i e)))
  (define i.bf (bf-complex (bf 0) (bf 1)))
  
  (make-poly-realfct [bf : Bigfloat]
                     [bf-complex : Bigfloat-Complex] bf-real-part bf-imag-part
                     bf bf+ bf- bf* bf/ bfabs
                     #:= bf=))


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

  (make-poly-cplxfct [ec : Exact-Number]
                     inexact->exact + - e* e/ #:= =)
  (ecpoly-from-roots 1+i 3 4/2-1/8i))
;****************************************************************************************************************************
(module+ flcpoly
  (require (only-in math/base float-complex?)
           math/flonum)

  (define (flc [a : Number]): Float-Complex (make-rectangular (fl (real-part a))(fl (imag-part a))))
  (define (flcsum [L : (Listof Float-Complex)]) : Float-Complex (flc (apply + L)))
  
  (make-poly-cplxfct [flc : Float-Complex]
                     flc + - * / #:= =))

;****************************************************************************************************************************
(module+ boolpoly
  (define (xor [a : Boolean][b : Boolean]) : Boolean (and (not (and a b)) (or a b)))
  (define (⊕ [a : Boolean][b : Boolean]) : Boolean (xor a b))
  (define (⊖ [a : Boolean][b : Boolean]) : Boolean (xor a b))
  (define (⊗ [a : Boolean][b : Boolean]) : Boolean (and a b))
  (define (⊘ [a : Boolean][b : Boolean]) : Boolean (and a b))
  (define (⊕sum [As : (Listof Boolean)]) : Boolean (for/fold ([a : Boolean #f])([b (in-list As)])(⊕ a b)))

  (define (make-boolean [a : Real]) : Boolean (= a 0))
  
  (make-poly-base+int/diff [b : Boolean]
                  make-boolean ⊕ ⊖ ⊗ ⊘ #:sum ⊕sum)
  (bpoly-scale (bpoly/ascending #t #f #t) #f)
  )
;|#