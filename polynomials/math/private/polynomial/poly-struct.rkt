#lang typed/racket/base

(require racket/vector
         racket/list)
(require "algebra.rkt"
         "monomoid.rkt"
         "poly-dict.rkt")

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
  (define V (make-vector (+ degree0 1) (algebra-zero alg)))
  (define degree : Nonnegative-Integer 0)
  (for* ([l (in-list cofs)]
         [i (in-value (monomoid-first (car l)))]
         [v (in-value (cadr l))]
        #:when (or ((algebra-t= alg) (vector-ref V i) (algebra-zero alg))
                   (raise-argument-error 'make-dense-poly "unique sets of exponents" cofs))
        #:unless ((algebra-t= alg) v (algebra-zero alg)))
    (when (< degree i) (set! degree i))
    (vector-set! V i v))
  (define D ((inst make-dense-dict TheType) (vector-take V (+ degree 1)) (algebra-zero alg)))
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
    (raise-argument-error 'make-sparse-poly "All groups of variable-exponents must have the same length" (list vars cofs)))
  (define H : (HashTable Monomoid-Exponents TheType) (make-hash))
  (define degree : Nonnegative-Integer  0)
  (for ([l (in-list cofs)]
        #:when (or (not (hash-ref H (car l) #f))
                   (raise-argument-error 'make-sparse-poly "unique sets of exponents" cofs))
        #:unless ((algebra-t= alg) (cadr l)(algebra-zero alg)))
    (let ([m (apply max (monomoid->list (car l)))])(when (< degree m)(set! degree m)))
    (hash-set! H (car l) (cadr l)))
  (poly (make-sparse-dict H (algebra-zero alg))
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
         (make-sparse-poly (list (list (monomoid-base->zero-exponent vars) (algebra-zero alg))) alg vars)
         (make-dense-poly (list (list (monomoid 0) (algebra-zero alg))) alg (or vars (monomoid 'x))))]
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

(: make-const-poly (All (TheType) (->* [TheType (Algebra TheType)][(Option Monomoid-Base)](Poly TheType))))
(define (make-const-poly cof alg [vars #f])
  (make-poly (list (list (if vars
                             (monomoid-base->zero-exponent vars)
                             (monomoid 0))
                         cof))
             alg vars))

(: poly->zero-poly (All (TheType)(-> (Poly TheType)(Poly TheType))))
(define (poly->zero-poly P)
  (make-const-poly (algebra-zero (poly-algebra P))
                   (poly-algebra P)
                   (poly-vars P)))

(: poly->one-poly (All (TheType)(-> (Poly TheType)(Poly TheType))))
(define (poly->one-poly P)
  (make-const-poly (algebra-one (poly-algebra P))
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
  (define zero (algebra-zero (poly-algebra P)))
  (define one (algebra-one (poly-algebra P)))
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
  (if (string=? S "") (format "~a" (algebra-zero (poly-algebra P))) S))
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
     (define zeroA (algebra-zero (poly-algebra PA)))
     (define eA0 (apply monomoid (make-list (poly-vars-len PA) 0)))
     (define zeroB (algebra-zero (poly-algebra PB)))
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
(define (poly*k-v P k v)
  (define t* (algebra-t* (poly-algebra P)))
  (poly-map (λ ([a : (List Monomoid-Exponents TheType)])
              (list (monomoid-exponents* (car a) k )(t* (cadr a) v)))
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
(: exp-hash (All (A) (-> A A (-> A A A) (-> Nonnegative-Integer A))))
(define (exp-hash H0 H1 fct*)
  (define H : (HashTable Nonnegative-Integer A) (make-hash))
  (hash-set! H 0 H0)
  (hash-set! H 1 H1)
  (: get-exp (-> Nonnegative-Integer A))
  (define (get-exp e)
    (cond
      [(hash-ref H e #f)]
      [(odd? e)
       (define P* (fct* H1 (get-exp (- e 1))))
       (hash-set! H e P*)
       P*]
      [else
       (define n/2 (assert (/ e 2) integer?))
       (define P* (fct* (get-exp n/2)(get-exp n/2)))
       (hash-set! H e P*)
       P*]))
  get-exp)
(: poly-substitute (All (TypeA TypeB) (-> (Poly TypeA) Symbol (Poly TypeB) (Poly TypeB))))
(define (poly-substitute PA var PB)
  (define ->t (algebra-->t (poly-algebra PB)))
  (define-values (vars nr remapA remapB)(monomoid-substitute (poly-vars PA) var (poly-vars PB)))
  (define PB* (poly-remap PB remapB vars))
  (define get-exp (exp-hash (poly->one-poly PB*) PB* (inst poly*p TypeB)))
  (for/fold : (Poly TypeB)
    ([P (poly->zero-poly PB*)])
    ([(k v)(in-coefficients PA)])
    (define e (monomoid-ref k nr))
    (poly+p P
            (poly*k-v (get-exp e)
                      (remapA k)(->t v)))))

;***********************************************************************************************************************
;* evaluate                                                                                                            *
;***********************************************************************************************************************
(: poly-evaluate (All (TheType) ((Poly TheType) TheType * -> TheType)))
(define (poly-evaluate P . xs)
  (unless (equal? (poly-vars-len P)(length xs))
    (raise-argument-error 'poly-evaluate "Coefficients don't map" (list (poly-vars P) '-> xs)))
  (define alg (poly-algebra P))
  (define zero (algebra-zero alg))
  (define t+ (algebra-t+ alg))
  (define t* (algebra-t* alg))
  (define exps (map (λ ([x : TheType])(exp-hash zero x t*)) xs))
  (define (× [v1 : TheType][vs : Monomoid-Exponents]) : TheType
    (for/fold ([S v1])
              ([v : Nonnegative-Integer vs]
               [e exps])
      (t* S (e v))))
  (for/fold : TheType
    ([S zero])
    ([(k v)(in-coefficients P)])
    (t+ S (× v k))))


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
     + * - / #:equal? =
     #:->t (λ (x) (if (number? x) x
                      (error "C-algebra: don't know how to convert to number:" x)))))
  (printf "definining operations over Boolean\n...\n\n")
  (define (xor [x : Boolean][y : Boolean]) (and (or x y)(not (and x y))))
  (define (⊕ [x : Boolean][y : Boolean]) (xor x y))
  (define (⊖ [x : Boolean][y : Boolean]) (xor x y))
  (define (⊗ [x : Boolean][y : Boolean]) (and x y))
  (define (⊘ [x : Boolean][y : Boolean]) (and x y))
  (define algebra-Bool ((inst make-algebra Boolean) ⊕ ⊗ ⊖ ⊘ #:->t (λ (x) (cond [(or (equal? x #f)(and (number? x)(= x 0))) #f][else #t]))))

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

  (printf "P2(1.2 3i)=~a\n" (poly-evaluate P2 1.2 +3i))

  (printf "\nSubstitute y in P2 by the boolean polynomial bP1\n")
  (printf "(poly-substitute P2 'y bP1)=~a\n" (poly->string (poly-substitute P2 'y bP1)))

  (printf "(the other way around would not work, since the operations over ℂ don't\n  know how to convert a Boolean to a Number\n  Notice that ->Bool is taking any value other than 0 or #f as #t)\n")
  )