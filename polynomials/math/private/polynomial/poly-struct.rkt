#lang typed/racket/base

(require racket/sequence
         racket/vector
         racket/list)
(require (for-syntax typed/racket/base))

;***********************************************************************************************************************
;* Algebra                                                                                                             *
;***********************************************************************************************************************

(struct (TheType) algebra
  ([->t  : (Any -> TheType)]
   [t=   : (TheType TheType -> Boolean)]
   [t+   : (TheType TheType -> TheType)]
   [t-   : (TheType TheType -> TheType)]
   [t*   : (TheType TheType -> TheType)]
   [t/   : (TheType TheType -> TheType)]
   [tsum : ((Listof TheType) -> TheType)]
   [Zero : TheType]
   [One  : TheType])
  #:type-name Algebra)

(: make-algebra (All (TheType)
                     (case-> (->* [(TheType TheType -> TheType)
                                   (TheType TheType -> TheType)
                                   (TheType TheType -> TheType)
                                   (TheType TheType -> TheType)]
                                  [#:->t (Option (Any -> TheType))
                                   #:i->t (Option (Integer -> TheType))
                                   #:Zero (Option TheType)
                                   #:One (Option TheType)
                                   #:equal? (TheType TheType -> Boolean)
                                   #:sum (Option ((Listof TheType) -> TheType))]
                                  (Algebra TheType)))))
(define (make-algebra t+ t- t* t/
                      #:->t [->t #f]
                      #:i->t [i->t #f]
                      #:Zero [Zero #f]
                      #:One [One  #f]
                      #:equal? [t=   equal?]
                      #:sum [tsum #f])
  (define-values (->t* Zero* One*)
    (cond
      [->t (values ->t (or Zero (->t 0))(or One (->t 1)))]
      [i->t (values (λ (x)
                      (cond
                        [(exact-integer? x) (i->t x)]
                        [else (raise-argument-error 'algebra "Unable to convert to thetype" x)]))
                    (or Zero (i->t 0))(or One (i->t 1)))]
      [(and Zero One)
       (values (λ (x)
                 (cond
                   [(integer? x)
                    (define +/- (if (< x 0) t- t+))
                    (for/fold : TheType ([s Zero])([i (in-range (abs x))])(+/- s One))]
                   [else (raise-argument-error 'algebra "Unable to convert to thetype" x)]))
               Zero One)]
      [else (raise-argument-error 'make-algebra "Either ->t or Zero and One need to be defined" (list ->t Zero One))]))
  (define tsum* (or tsum (λ ([x : (Listof TheType)]) : TheType (for/fold ([s Zero*])([v (in-list x)])(t+ s v)))))
  (algebra ->t* t= t+ t- t* t/ tsum* Zero* One*))

;***********************************************************************************************************************
;* Monomoid                                                                                                            *
;***********************************************************************************************************************
(define-type Monomoid-Exponents (Vectorof Nonnegative-Integer))
(define-type Monomoid-Base (Vectorof Symbol))
(: monomoid (case-> (->* () #:rest Nonnegative-Integer Monomoid-Exponents)
             (->* () #:rest Symbol Monomoid-Base)))
(define (monomoid . x) (list->vector x))
(define (monomoid-base->zero-exponent [b : Monomoid-Base]): Monomoid-Exponents (make-vector (monomoid-length b) 0))

(: list->monomoid (case-> (-> (Listof Nonnegative-Integer) Monomoid-Exponents)(-> (Listof Symbol) Monomoid-Base)))
(define (list->monomoid l) (list->vector l))

(: monomoid->list (case-> (-> Monomoid-Exponents (Listof Nonnegative-Integer))(-> Monomoid-Base (Listof Symbol))))
(define (monomoid->list v) (vector->list v))

(define (monomoid-length [x : (U Monomoid-Exponents Monomoid-Base)]) : Nonnegative-Integer (vector-length x))

(: monomoid-ref (case-> (-> Monomoid-Exponents Nonnegative-Integer Nonnegative-Integer)(-> Monomoid-Base Nonnegative-Integer Symbol)))
(define (monomoid-ref x i) (vector-ref x i))

(: monomoid-first (case-> (-> Monomoid-Exponents Nonnegative-Integer)(-> Monomoid-Base Symbol)))
(define (monomoid-first x)(monomoid-ref x 0))

(define (monomoid-has? [vars : Monomoid-Base][var : Symbol]) : (Option Nonnegative-Integer)
  (for/or ([v (in-vector vars)]
           [i : Nonnegative-Integer (in-naturals)])
    (and (equal? var v)i)))

(define (monomoid-combine [b1 : Monomoid-Base][b2 : Monomoid-Base])
  : (Values Monomoid-Base
            (-> Monomoid-Exponents Monomoid-Exponents)
            (-> Monomoid-Exponents Monomoid-Exponents))
  (define vars (list->monomoid (remove-duplicates (append (monomoid->list b1)(monomoid->list b2)))))
  (define vars-len (monomoid-length vars))
  (define dif (make-list (- vars-len (monomoid-length b1)) 0))
  (define k-map : (HashTable Symbol Nonnegative-Integer)(make-hash))
  (for ([x vars])(cond [(monomoid-has? b2 x) => (λ (i) (hash-set! k-map x i))]))
  (define (remap1 [k : Monomoid-Exponents])(list->monomoid (append (monomoid->list k) dif)))
  (define (remap2 [k : Monomoid-Exponents]) : Monomoid-Exponents
    (list->monomoid (for/list : (Listof Nonnegative-Integer)
               ([x vars])
               (cond [(hash-ref k-map x #f) => (λ (i) (monomoid-ref k i))]
                     [else 0]))))
  (values vars remap1 remap2))

(define (monomoid-substitute [b1 : Monomoid-Base][var : Symbol][b2 : Monomoid-Base])
  : (Values Monomoid-Base
            Nonnegative-Integer
            (-> Monomoid-Exponents Monomoid-Exponents)
            (-> Monomoid-Exponents Monomoid-Exponents))
  (define nr (monomoid-has? b1 var))
  (cond
    [nr
     (define-values (a b)(split-at (monomoid->list b1) nr))
     (define b1* (list->monomoid (append a (cdr b))))
     (define (remove [e1 : Monomoid-Exponents]) : Monomoid-Exponents
       (define-values (a b)(split-at (monomoid->list e1) nr))
       (list->monomoid (append a (cdr b))))
     (define-values (vars rebase1 rebase2)(monomoid-combine b1* b2))
     (values vars
             nr
             (λ ([b1 : Monomoid-Exponents]) : Monomoid-Exponents
               (rebase1 (remove b1)))
             rebase2)]
    [else
     (raise-argument-error 'monomoid-substitute (format "Var of first base ~a" b1) var)]))

(define (monomoid-exponents* [e0 : Monomoid-Exponents][e1 : Monomoid-Exponents]) : Monomoid-Exponents
  (unless (= (monomoid-length e0)(monomoid-length e1)) (raise-argument-error 'e+ "monomoid-exponent-sets should have equal length" (list '≠ e0 e1)))
  (for/vector : Monomoid-Exponents
    ([e0i (in-vector e0)]
     [e1i (in-vector e1)])
    (+ e0i e1i)))

;***********************************************************************************************************************
;* Poly-dict: mapping monomoid to coefficients                                                                         *
;***********************************************************************************************************************
(define-type p-dict (All (TheType) (case-> (Monomoid-Exponents -> TheType)
                                           (      -> (Sequenceof Monomoid-Exponents TheType))
                                           
                                           ('get 'size -> Nonnegative-Integer)
                                           ('get 'copy -> (p-dict TheType))
                                           ('get 'list -> (Listof (List Monomoid-Exponents TheType)))
                                           ('get Symbol -> Any)
                                           ('set Monomoid-Exponents TheType -> (p-dict TheType)))))

(: make-dense-dict (All (TheType) ((Vectorof TheType) TheType -> (p-dict TheType))))
(define (make-dense-dict V zero)
  (case-lambda
    [(x) (define i (monomoid-first x))
         (if (< -1 i (vector-length V)) (vector-ref V (monomoid-first x)) zero)]
    [() (in-parallel ((inst sequence-map Monomoid-Exponents Nonnegative-Integer)
                      (λ ([x : Nonnegative-Integer]) : Monomoid-Exponents (monomoid x))
                      (in-naturals))
                     (in-vector V))]
    [(get x)
     (case x
       [(size)(vector-length V)]
       [(copy)(make-dense-dict (vector-copy V) zero)]
       [(list)(for/list : (Listof (List Monomoid-Exponents TheType))
                ([i : Nonnegative-Integer (in-naturals)]
                 [v (in-vector V)])
                (list (monomoid i) v))])]
    [(set i v)
     (define V+ (vector-copy V))
     (vector-set! V+ (monomoid-first i) v)
     (make-dense-dict V+ zero)]))

(: make-sparse-dict (All (TheType) ((HashTable Monomoid-Exponents TheType) TheType -> (p-dict TheType))))
(define (make-sparse-dict H zero)
  (case-lambda
    [(x) (hash-ref H x (λ () zero))]
    [() ((inst in-hash Monomoid-Exponents TheType) H)]
    [(get x)
     (case x
       [(size)(hash-count H)]
       [(copy)(make-sparse-dict (hash-copy H) zero)]
       [(list)(for/list : (Listof (List Monomoid-Exponents TheType))
                ([(k v)(in-hash H)])
                (list k v))])]
    [(set i v)
     (define H+ (hash-copy H))
     (hash-set! H+ i v)
     (make-sparse-dict H+ zero)]))
;***********************************************************************************************************************
;* basic poly struct                                                                                                   *
;***********************************************************************************************************************
(struct (TheType) poly
  ([coefficients : (p-dict TheType)]
   [vars         : Monomoid-Base]
   [vars-len     : Nonnegative-Integer]
   [degree       : Nonnegative-Integer]
   [algebra      : (Algebra TheType)])
  #:type-name Poly)
;***********************************************************************************************************************
;* dense / sparse / global contstructor for poly                                                                       *
;***********************************************************************************************************************
(: make-dense-poly (All (TheType) (->* [(Listof (List Monomoid-Exponents TheType))
                                        (Algebra TheType)]
                                       [(Option Monomoid-Base)]
                                       (Poly TheType))))
(define (make-dense-poly cofs alg [var #f])
  (define degree0 (apply max ((inst map Nonnegative-Integer (List Monomoid-Exponents TheType))
                             (λ (x) (monomoid-first (car x))) cofs)))
  (define V (make-vector (+ degree0 1) (algebra-Zero alg)))
  (define degree : Nonnegative-Integer 0)
  (for* ([l (in-list cofs)]
         [i (in-value (monomoid-first (car l)))]
         [v (in-value (cadr l))]
        #:when (or ((algebra-t= alg) (vector-ref V i) (algebra-Zero alg))
                   (raise-argument-error 'make-dense-poly "unique sets of exponents" cofs))
        #:unless ((algebra-t= alg) v (algebra-Zero alg)))
    (when (< degree i) (set! degree i))
    (vector-set! V i v))
  (define D ((inst make-dense-dict TheType) (vector-take V (+ degree 1)) (algebra-Zero alg)))
  (poly D
        (or var (monomoid 'x))
        1
        degree
        alg))

(: make-sparse-poly (All (TheType) (->* [(Listof (List Monomoid-Exponents TheType))
                                         (Algebra TheType)]
                                        [(Option Monomoid-Base)]
                                        (Poly TheType))))
(define (make-sparse-poly cofs alg [vars #f])
  (define vars-len (monomoid-length (caar cofs)))
  (define vars* (or vars (list->monomoid (for/list : (Listof Symbol)
                                    ([i (in-range vars-len)])
                                    (string->symbol (format "x_~a" i))))))
  (unless (and (if vars (= (monomoid-length vars*) vars-len) #t)
               (andmap (λ ([x : (List Monomoid-Exponents TheType)])(= (monomoid-length (car x)) vars-len)) cofs))
    (raise-argument-error 'make-sparse-poly "All groups of variable-exponents musth have the same length" (list vars cofs)))
  (define H : (HashTable Monomoid-Exponents TheType) (make-hash))
  (define degree : Nonnegative-Integer  0)
  (for ([l (in-list cofs)]
        #:when (or (not (hash-ref H (car l) #f))
                   (raise-argument-error 'make-sparse-poly "unique sets of exponents" cofs))
        #:unless ((algebra-t= alg) (cadr l)(algebra-Zero alg)))
    (let ([m (apply max (monomoid->list (car l)))])(when (< degree m)(set! degree m)))
    (hash-set! H (car l) (cadr l)))
  (poly (make-sparse-dict H (algebra-Zero alg))
        vars*
        vars-len
        degree
        alg))

(: make-poly (All (TheType) (->* [(U (Listof (List Monomoid-Exponents TheType))(Listof (List (Listof Nonnegative-Integer) TheType)))
                                  (Algebra TheType)]
                                 [(Option Monomoid-Base)]
                                 (Poly TheType))))
(define (make-poly cofs* alg [vars #f])
  (cond
    [(empty? cofs*)
     (if (and vars (< 1 (monomoid-length vars)))
         (make-sparse-poly (list (list (monomoid-base->zero-exponent vars) (algebra-Zero alg))) alg vars)
         (make-dense-poly (list (list (monomoid 0) (algebra-Zero alg))) alg (or vars (monomoid 'x))))]
    [else
     (define cofs (if (list? (caar cofs*))
                      (map (λ ([x : (List (Listof Nonnegative-Integer) TheType)]) : (List Monomoid-Exponents TheType)
                             (cons (apply monomoid (car x)) (cdr x)))
                           cofs*)
                      cofs*))
     (define vars-len (or (and vars (monomoid-length vars))
                          (monomoid-length (caar cofs))))
     (cond
       [(< 1 vars-len) (make-sparse-poly cofs alg vars)]
       [else ;(andmap (λ ([x : (Listof (List Monomoid-Exponents ))]) (empty? (cdr (car x)))) cofs)
        (define-values (deg len)
          (for*/fold : (Values Nonnegative-Integer Nonnegative-Integer)
            ([deg : Nonnegative-Integer 0]
             [len : Nonnegative-Integer 0])
            ([l : (List Monomoid-Exponents TheType) (in-list cofs)]
             [k (in-value (car l))])
            (values (max deg (monomoid-first k)) (+ len 1))))
        (if (< (/ deg len) 8/10)
            (make-sparse-poly cofs alg vars)
            (make-dense-poly cofs alg vars))])]))

(: poly->zero-poly (All (TheType)(-> (Poly TheType)(Poly TheType))))
(define (poly->zero-poly P)
  (make-poly (list (list (monomoid-base->zero-exponent (poly-vars P))(algebra-Zero (poly-algebra P))))
             (poly-algebra P)
             (poly-vars P)))

(: poly->one-poly (All (TheType)(-> (Poly TheType)(Poly TheType))))
(define (poly->one-poly P)
  (make-poly (list (list (monomoid-base->zero-exponent (poly-vars P))(algebra-One (poly-algebra P))))
             (poly-algebra P)
             (poly-vars P)))

(: poly-remap (All (TheType)(-> (Poly TheType)(-> Monomoid-Exponents Monomoid-Exponents)(Option Monomoid-Base)(Poly TheType))))
(define (poly-remap P remap vars)
  (poly-map (λ ([a : (List Monomoid-Exponents TheType)]):(List Monomoid-Exponents TheType)(cons (remap (car a))(cdr a))) P #f #f vars))

;***********************************************************************************************************************
;* coefficient acces / set / copy                                                                                      *
;***********************************************************************************************************************
(: poly-copy (All (TheType) (-> (Poly TheType) (Poly TheType))))
(define (poly-copy P) (struct-copy poly P [coefficients ((poly-coefficients P) 'get 'copy)]))

(: poly-set (All (TheType) (-> (Poly TheType) Monomoid-Exponents TheType (Poly TheType))))
(define (poly-set P k v) (struct-copy poly P [coefficients ((poly-coefficients P) 'set k v)]))

(: in-coefficients (All (TheType) (-> (Poly TheType) (Sequenceof Monomoid-Exponents TheType))))
(define (in-coefficients P)((poly-coefficients P)))

(: poly-coefficient (All (TheType) (-> (Poly TheType) Monomoid-Exponents TheType)))
(define (poly-coefficient P k) ((poly-coefficients P) k))

(: poly->coefficient-list (All (TheType) (-> (Poly TheType) (Listof (List Monomoid-Exponents TheType)))))
(define (poly->coefficient-list P) ((poly-coefficients P) 'get 'list))
;***********************************************************************************************************************
;* string representation of poly                                                                                       *
;***********************************************************************************************************************
(: poly->string (All (TheType) (-> (Poly TheType) String)))
(define (poly->string P)
  (define zero (algebra-Zero (poly-algebra P)))
  (define one (algebra-One (poly-algebra P)))
  (define vars (poly-vars P))
  (define (make-term [v : TheType][k : Monomoid-Exponents]) : String
    (cond
      [(equal? v zero) ""]
      [else
       (define b
         (add-between (for/list : (Listof String)
                        ([i k]
                         [x vars]
                         #:unless (= i 0))
                        (format "~a~a" x (if (= i 1) "" (format "^~a" i))))
                      "."))
       (define b* (if (equal? b '()) (list (format "~a^0" (monomoid-first vars))) b))
       (cond
         [(equal? v one)(format "~a" b*)]
         [else (format "~a.~a" v b*)])]))
  (define S
    (apply
     string-append
     (for/list : (Listof String)
       ([([k : Monomoid-Exponents][v : TheType]) (in-coefficients P)]
        [i (in-naturals)])
       (define S (make-term v k))
       (cond
         [(equal? S "") S]
         [(= i 0) S]
         [(not (real? v)) (string-append " +"S)]
         [(<= 0 v) (string-append " +" S)]
         [else (string-append " " S)]))))
  (if (string=? S "") (format "~a" (algebra-Zero (poly-algebra P))) S))
;***********************************************************************************************************************
;* map over the poly-coefficients                                                                                      *
;***********************************************************************************************************************
(: poly-map (All (TypeA TypeB TypeC)
                 (case-> (-> (Monomoid-Exponents (List Monomoid-Exponents TypeA) (List Monomoid-Exponents TypeB) -> (List Monomoid-Exponents TypeC))
                             (Poly TypeA) (Poly TypeB) (Algebra TypeC) (Option Monomoid-Base)
                             (Poly TypeC))
                         (-> (Monomoid-Exponents (List Monomoid-Exponents TypeA) (List Monomoid-Exponents TypeB) -> (List Monomoid-Exponents TypeA))
                             (Poly TypeA) (Poly TypeB) #f (Option Monomoid-Base)
                             (Poly TypeA))
                         (-> ((List Monomoid-Exponents TypeA) -> (List Monomoid-Exponents TypeC))
                             (Poly TypeA) #f (Algebra TypeC) (Option Monomoid-Base)
                             (Poly TypeC))
                         (-> ((List Monomoid-Exponents TypeA) -> (List Monomoid-Exponents TypeA))
                             (Poly TypeA) #f #f (Option Monomoid-Base)
                             (Poly TypeA)))))
(define (poly-map fct PA PB alg vars*)
  (cond
    [PB
     (define-values (vars remapA remapB) (monomoid-combine (poly-vars PA)(poly-vars PB)))
     (define ks : (HashTable Monomoid-Exponents (Pair (Option Monomoid-Exponents)(Option Monomoid-Exponents)))(make-hash))
     (for ([(k v)(in-coefficients PA)])
       (hash-set! ks (remapA k) (cons k #f)))
     (for ([(k v)(in-coefficients PB)])
       (hash-update! ks (remapB k)
                     (λ ([x : (Pair (Option Monomoid-Exponents)(Option Monomoid-Exponents))])
                       (cons (car x) k))
                     (λ () (cons #f #f))))
     (define zeroA (algebra-Zero (poly-algebra PA)))
     (define eA0 (apply monomoid (make-list (poly-vars-len PA) 0)))
     (define zeroB (algebra-Zero (poly-algebra PB)))
     (define eB0 (apply monomoid (make-list (poly-vars-len PB) 0)))

     (cond
       [alg
        ((inst make-poly TypeC)
         (for/list : (Listof (List Monomoid-Exponents TypeC))
           ([(k v) (in-hash ks)])
           (fct k
                (if (car v) (list (car v) (poly-coefficient PA (car v))) (list eA0 zeroA))
                (if (cdr v) (list (cdr v) (poly-coefficient PB (cdr v))) (list eB0 zeroB))))
         alg
         (or vars* vars))]
       [else
        ((inst make-poly TypeA)
         (for/list : (Listof (List Monomoid-Exponents TypeA))
           ([(k v) (in-hash ks)])
           (fct k
                (if (car v) (list (car v) (poly-coefficient PA (car v))) (list eA0 zeroA))
                (if (cdr v) (list (cdr v) (poly-coefficient PB (cdr v))) (list eB0 zeroB))))
         (poly-algebra PA)
         (or vars* vars))])]
    [alg
     (make-poly
      (map fct (poly->coefficient-list PA))
      alg
      (or vars* (poly-vars PA)))]
    [else
     (make-poly
      (map fct (poly->coefficient-list PA))
      (poly-algebra PA)
      (or vars* (poly-vars PA)))]))
;***********************************************************************************************************************
;* addition                                                                                                            *
;***********************************************************************************************************************
(: poly+p (All (TheType) (-> (Poly TheType) (Poly TheType) (Poly TheType))))
(define (poly+p PA PB)
  (define t+ (algebra-t+ (poly-algebra PA)))
  (poly-map (λ ([k : Monomoid-Exponents][a : (List Monomoid-Exponents TheType)][b : (List Monomoid-Exponents TheType)])
              (list k (t+ (cadr a)(cadr b))))
            PA PB #f #f))
(: poly+ (All (TheType) (->* [(Poly TheType)] #:rest (Poly TheType) (Poly TheType))))
(define (poly+ PA . PBs)
  (for/fold ([P PA])
            ([Pi (in-list PBs)])
    (poly+p P Pi)))
;***********************************************************************************************************************
;* subraction                                                                                                          *
;***********************************************************************************************************************
(: poly- (All (TheType) (->* [(Poly TheType)] #:rest (Poly TheType) (Poly TheType))))
(define (poly- PA . PBs)
  (define P0 (if (empty? PBs) (make-poly '() (poly-algebra PA)(poly-vars PA)) PA))
  (define P1s (if (empty? PBs) (list PA) PBs))
  (define t- (algebra-t- (poly-algebra PA)))
  (poly-map (λ ([k : Monomoid-Exponents][a : (List Monomoid-Exponents TheType)][b : (List Monomoid-Exponents TheType)])
              (list k (t- (cadr a)(cadr b))))
            P0 (apply poly+ P1s) #f #f))
;***********************************************************************************************************************
;* scale                                                                                                               *
;***********************************************************************************************************************
(: poly*s (All (TheType) (-> (Poly TheType) TheType (Poly TheType))))
(define (poly*s PA s)
  (define t* (algebra-t* (poly-algebra PA)))
  (poly-map (λ ([a : (List Monomoid-Exponents TheType)])
              (list (car a) (t* (cadr a) s)))
            PA #f #f #f))
(: poly/s (All (TheType) (-> (Poly TheType) TheType (Poly TheType))))
(define (poly/s PA s)
  (define t/ (algebra-t/ (poly-algebra PA)))
  (poly-map (λ ([a : (List Monomoid-Exponents TheType)])
              (list (car a) (t/ (cadr a) s)))
            PA #f #f #f))
(define poly-scale poly*s)

;***********************************************************************************************************************
;* multiplication                                                                                                      *
;***********************************************************************************************************************
(: poly*k-v (All (TheType) (-> (Poly TheType) Monomoid-Exponents TheType (Poly TheType))))
(define (poly*k-v P v s)
  (define t* (algebra-t* (poly-algebra P)))
  (poly-map (λ ([a : (List Monomoid-Exponents TheType)])
              (list (monomoid-exponents* (car a) v )(t* (cadr a) s)))
            P #f #f #f))
(: poly*p (All (TheType) (-> (Poly TheType) (Poly TheType) (Poly TheType))))
(define (poly*p PA PB)
  (define t+ (algebra-t+ (poly-algebra PA)))
  (define t* (algebra-t* (poly-algebra PA)))
  (define-values (vars P0 P1)
    (cond
      [(equal? (poly-vars PA)(poly-vars PB))
       (values (poly-vars PA) PA PB)]
      [else
       (define-values (vars remapA remapB)(monomoid-combine (poly-vars PA)(poly-vars PB)))
       (values vars (poly-remap PA remapA vars) (poly-remap PB remapB vars))]))
  (for/fold : (Poly TheType)
   ([P (make-poly '() (poly-algebra PA) vars)])
   ([(k v) (in-coefficients P1)])
    (poly+p P (poly*k-v P0 k v))))
(: poly* (All (TheType) (->* [(Poly TheType)] #:rest (Poly TheType) (Poly TheType))))
(define (poly* PA . PBs)
  (for/fold ([P PA])
            ([Pi (in-list PBs)])
    (poly*p P Pi)))

;***********************************************************************************************************************
;* exponentiation                                                                                                      *
;***********************************************************************************************************************
(: poly-expt (All (TheType) (-> (Poly TheType) Nonnegative-Integer (Poly TheType))))
(define (poly-expt P e)
  (cond
    [(= 0 e) (poly->one-poly P)]
    [(= 1 e) P]
    [(= 2 e) (poly*p P P)]
    [(odd? e)
     (poly*p P (poly-expt P (- e 1)))]
    [else
     (define n/2 (assert (/ e 2) integer?))
     (define P^2 (poly* P P))
     (poly-expt P^2 n/2)]))

;***********************************************************************************************************************
;* substitute: results in a poly over algebra of B                                                                     *
;***********************************************************************************************************************
(: poly-substitute (All (TypeA TypeB) (-> (Poly TypeA) Symbol (Poly TypeB) (Poly TypeB))))
(define (poly-substitute PA var PB)
  (define ->t (algebra-->t (poly-algebra PB)))
  (define-values (vars nr remapA remapB)(monomoid-substitute (poly-vars PA) var (poly-vars PB)))
  (define PB* (poly-remap PB remapB vars))
  (define H : (HashTable Nonnegative-Integer (Poly TypeB)) (make-hash))
  (hash-set! H 1 PB*)
  (hash-set! H 0 (poly->one-poly PB*))
  (: get-exp (-> Nonnegative-Integer (Poly TypeB)))
  (define (get-exp e)
    (cond
      [(hash-ref H e #f)]
      [(odd? e)
       (define P* (poly*p PB* (get-exp (- e 1))))
       (hash-set! H e P*)
       P*]
      [else
       (define n/2 (assert (/ e 2) integer?))
       (define P* (poly*p (get-exp n/2)(get-exp n/2)))
       (hash-set! H e P*)
       P*]))
  (for/fold : (Poly TypeB)
    ([P (poly->zero-poly PB*)])
    ([(k v)(in-coefficients PA)])
    (define e (monomoid-ref k nr))
    (poly+p P
            (poly*k-v (get-exp e)
                      (remapA k)(->t v)))))


;***********************************************************************************************************************
(module+ test0
  (define P0 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 3 2) 1)(list (monomoid 2 0) 3))
                               ((inst make-algebra Number) + - * / #:i->t values)
                               (monomoid 'x 'y)))
  (define P1 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 4 2) 1))
                               ((inst make-algebra Number) + - * / #:i->t values)
                               (monomoid 'z 'x)))
  (poly-degree P0)
  (poly->string P0)
  (poly-degree P1)
  (poly->string P1)
  (println "P0+P1")
  (define P2 (poly+p P0 P1))
  (poly-degree P2)
  (poly->string P2)
  (println "P0*2")
  (define P3 (poly-scale P0 2))
  (poly-degree P3)
  (poly->string P3)
  )

(module+ test
  (printf "defining operations over ℂ\n")
  (define algebra-C
    ((inst make-algebra Number)
     + - * / #:equal? =
     #:->t (λ (x) (if (number? x) x
                      (error "C-algebra: don't know how to convert to number:" x)))))
  (printf "definining operations over Boolean\n...\n\n")
  (define (xor [x : Boolean][y : Boolean]) (and (or x y)(not (and x y))))
  (define (⊕ [x : Boolean][y : Boolean]) (xor x y))
  (define (⊖ [x : Boolean][y : Boolean]) (xor x y))
  (define (⊗ [x : Boolean][y : Boolean]) (and x y))
  (define (⊘ [x : Boolean][y : Boolean]) (and x y))
  (define algebra-Bool ((inst make-algebra Boolean) ⊕ ⊖ ⊗ ⊘ #:->t (λ (x) (cond [(or (equal? x #f)(and (number? x)(= x 0))) #f][else #t]))))

  ;some shorthand
  (: Cpoly/ascending (->* [][#:base Symbol] #:rest Number (Poly Number)))
  (define (Cpoly/ascending #:base [var 'x] . vs)
    (make-dense-poly (for/list : (Listof (List Monomoid-Exponents Number))
                       ([v (in-list vs)]
                        [i : Nonnegative-Integer (in-naturals)])
                       (list (monomoid i) v))
                     algebra-C
                     (monomoid var)))

  ;my favorite shorthand
  (: Cpoly/descending (->* [][#:base Symbol] #:rest Number (Poly Number)))
  (define (Cpoly/descending #:base [var 'x] . vs)
    (make-dense-poly (for/list : (Listof (List Monomoid-Exponents Number))
                       ([v (in-list (reverse vs))]
                        [i : Nonnegative-Integer (in-naturals)])
                       (list (monomoid i) v))
                     algebra-C
                     (monomoid var)))

  (printf "defining and printing some polynomials\n")
  (define bP0 (make-poly '(((3) #t)((0)#t)) algebra-Bool))
  (printf "bP0:=~a\n" (poly->string bP0))
  (define bP1 (make-poly '(((1 1)#t)((2 0)#t)) algebra-Bool (monomoid 'x 'y)))
  (printf "bP1:=~a\n" (poly->string bP1))

  (printf "bP0+bP1=~a\n" (poly->string (poly+ bP0 bP1)))
  (printf "bP0*bP1=~a\n" (poly->string (poly* bP0 bP1)))
  (printf "bP1^2  =~a\n" (poly->string (poly-expt bP1 2)))

  (printf "\nNow in ℂ\n")
  (define P0 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 3 2) 1)(list (monomoid 2 0) 3))
                               ((inst make-algebra Number) + - * / #:i->t values)
                               (monomoid 'x 'y)))
  (printf "P0:=~a\n" (poly->string P0))
  (define P1 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 4 2) 1))
                               ((inst make-algebra Number) + - * / #:i->t values)
                               (monomoid 'z 'x)))
  (printf "P1:=~a\n" (poly->string P1))
  (define P2 (make-poly '(((1 3) 1)((1 0)1)((0 0)1)) algebra-C (monomoid 'x 'y)))
  (printf "P2:=~a\n" (poly->string P2))
  (define P3 (Cpoly/descending #:base 'y 2 0 1))
  (printf "P3:=~a\n" (poly->string P3))

  (printf "P0+P1=~a\n" (poly->string (poly+ P0 P1)))
  (printf "P1*P2=~a\n" (poly->string (poly* P1 P2)))
  (printf "P3^2  =~a\n" (poly->string (poly-expt P3 2)))

  (printf "\nSubstitute y in P2 by the boolean polynomial bP1\n")
  (printf "(poly-substitute P2 'y bP1)=~a\n" (poly->string (poly-substitute P2 'y bP1)))

  (printf "(the other way around would not work, since the operations over ℂ don't\n  know how to convert a Boolean to a Number\n  Notice that ->Bool is taking any value other than 0 or #f as #t)\n")
  )