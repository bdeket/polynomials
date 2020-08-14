#lang typed/racket/base

(require racket/vector
         racket/list
         (for-syntax racket/base
                     racket/syntax))
(require "algebra.rkt"
         "monomoid.rkt"
         "poly-dict.rkt")

(provide make-poly poly-from-roots Poly
         poly-degree poly-vars poly-vars-len
         poly-copy poly-set in-coefficients poly-coefficient poly-=
         poly->string
         poly-1-map poly-2-map poly-n-map poly-remap poly-realg poly-remove-unused-base-vars
         poly+ poly-scale poly* poly- poly-quotient/remainder poly-expt
         poly-substitute
         poly-diff poly-int
         poly-evaluate
         with-algebra
         (all-from-out "algebra.rkt") monomoid)

;***********************************************************************************************************************
;* basic poly struct                                                                                                   *
;***********************************************************************************************************************
(struct (A) poly
  ([coefficients : (p-dict A)]
   [vars         : Monomoid-Base]
   [vars-len     : Nonnegative-Integer]
   [degree       : Nonnegative-Integer])
  #:type-name Poly)

;***********************************************************************************************************************
;* dense / sparse / global contstructor for poly                                                                       *
;***********************************************************************************************************************
(define #:forall (A) (make-dense-poly [alg : (Algebra+* A)]
                                      [cofs : (Listof (List Monomoid-Exponents A))]
                                      [var : (Option Monomoid-Base) #f]) : (Poly A)
  (define zero (algebra-zero alg))
  (define degree0 (apply max ((inst map Nonnegative-Integer (List Monomoid-Exponents A))
                              (λ (x) (monomoid-first (car x))) cofs)))
  (define V (make-vector (+ degree0 1) zero))
  (define degree : Nonnegative-Integer 0)
  (for* ([l (in-list cofs)]
         [i (in-value (monomoid-first (car l)))]
         [v (in-value (cadr l))]
         #:when (or ((algebra-t= alg) (vector-ref V i) zero)
                    (raise-argument-error 'make-dense-poly "unique sets of exponents" cofs))
         #:unless ((algebra-t= alg) v zero))
    (when (< degree i) (set! degree i))
    (vector-set! V i v))
  (define D ((inst make-dense-dict A) (vector-take V (+ degree 1)) zero))
  (poly D
        (or var monomoid-x)
        1
        degree))

(define #:forall (A) (make-sparse-poly [alg : (Algebra+* A)]
                                       [cofs : (Listof (List Monomoid-Exponents A))]
                                       [vars : (Option Monomoid-Base)]) : (Poly A)
  (define zero (algebra-zero alg))
  (define vars-len (monomoid-length (caar cofs)))
  (define vars* (or vars (make-monomoid-base vars-len)))
  (unless (and (if vars (= (monomoid-length vars*) vars-len) #t)
               (andmap (λ ([x : (List Monomoid-Exponents A)])(= (monomoid-length (car x)) vars-len)) cofs))
    (raise-argument-error 'make-sparse-poly "All groups of variable-exponents must have the same length" (list vars cofs)))
  (define H : (HashTable Monomoid-Exponents A) (make-hash))
  (define degree : Nonnegative-Integer  0)
  (for ([l (in-list cofs)]
        #:when (or (not (hash-ref H (car l) #f))
                   (raise-argument-error 'make-sparse-poly "unique sets of exponents" cofs))
        #:unless ((algebra-t= alg) (cadr l) zero))
    (let ([m (apply max (monomoid->list (car l)))])(when (< degree m)(set! degree m)))
    (hash-set! H (car l) (cadr l)))
  (poly (make-sparse-dict H zero)
        vars*
        vars-len
        degree))

(define-type Cofs (All (A)(U (Listof (List Monomoid-Exponents A))(Listof (List (Listof Nonnegative-Integer) A)))))
(define #:forall (A) (make-poly [alg : (Algebra+* A)]
                                [cofs* : (Cofs A)]
                                [vars : (Option Monomoid-Base) #f]) : (Poly A)
  (cond
    [(empty? cofs*)
     (define zero (algebra-zero alg))
     (if (and vars (< 1 (monomoid-length vars)))
         (make-sparse-poly alg (list (list (monomoid-base->zero-exponent vars) zero)) vars)
         (make-dense-poly alg (list (list monomoid-0 zero)) (or vars monomoid-x)))]
    [else
     (define cofs (if (list? (caar cofs*))
                      (map (λ ([x : (List (Listof Nonnegative-Integer) A)]) : (List Monomoid-Exponents A)
                             (cons (apply monomoid (car x)) (cdr x)))
                           cofs*)
                      cofs*))
     (define vars-len (or (and vars (monomoid-length vars))
                          (monomoid-length (caar cofs))))
     (cond
       [(< 1 vars-len) (make-sparse-poly alg cofs vars)]
       [else ;(andmap (λ ([x : (Listof (List Monomoid-Exponents ))]) (empty? (cdr (car x)))) cofs)
        (define-values (deg len)
          (for*/fold : (Values Nonnegative-Integer Nonnegative-Integer)
            ([deg : Nonnegative-Integer 0]
             [len : Nonnegative-Integer 0])
            ([l : (List Monomoid-Exponents A) (in-list cofs)]
             [k (in-value (car l))])
            (values (max deg (monomoid-first k)) (+ len 1))))
        (if (or (= deg 0)(< (/ len deg) 8/10))
            (make-sparse-poly alg cofs (or vars monomoid-x))
            (make-dense-poly alg cofs (or vars monomoid-x)))])]))

(define #:forall (A) (make-const-poly [alg : (Algebra+* A)]
                                      [cof : A]
                                      [vars : (Option Monomoid-Base) #f]) : (Poly A)
  (make-poly alg
             (list (list (if vars
                             (monomoid-base->zero-exponent vars)
                             monomoid-0)
                         cof))
             vars))

(: make-zero-poly (All (A B) (->* [(Algebra+* A)][(U #f (Poly B) Monomoid-Base)] (Poly A))))
(define (make-zero-poly alg [b? #f])
  (make-const-poly alg
                   (algebra-zero alg)
                   (cond
                     [(poly? b?) (poly-vars b?)]
                     [(vector? b?) b?]
                     [else #f])))

(: make-one-poly (All (A B) (->* [(Algebra+* A)][(U #f (Poly B) Monomoid-Base)] (Poly A))))
(define (make-one-poly alg [b? #f])
  (make-const-poly alg
                   (algebra-one alg)
                   (cond
                     [(poly? b?) (poly-vars b?)]
                     [(vector? b?) b?]
                     [else #f])))

;***********************************************************************************************************************
;* coefficient acces / set / copy                                                                                      *
;***********************************************************************************************************************
(: poly-copy (All (A) (-> (Poly A) (Poly A))))
(define (poly-copy P) (struct-copy poly P [coefficients ((p-dict-copy (poly-coefficients P)))]))

(: poly-set (All (A) (-> (Poly A) Monomoid-Exponents A (Poly A))))
(define (poly-set P k v) (struct-copy poly P [coefficients ((p-dict-set (poly-coefficients P)) k v)]))

(: in-coefficients (All (A) (-> (Poly A) (Sequenceof Monomoid-Exponents A))))
(define (in-coefficients P)((p-dict-sequence (poly-coefficients P))))

(: poly-coefficient (All (A) (-> (Poly A) Monomoid-Exponents A)))
(define (poly-coefficient P k)
  (unless (= (monomoid-length k) (poly-vars-len P)) (raise-argument-error 'poly-coefficient "same base" k))
  ((p-dict-term (poly-coefficients P)) k))

(: poly->coefficient-list (All (A) (-> (Poly A) (Listof (List Monomoid-Exponents A)))))
(define (poly->coefficient-list P) ((p-dict-list (poly-coefficients P))))

(define #:forall (A B C)(poly-= [alg : (Algebra A)][PA : (Poly B)][PB : (Poly C)])
  ;TODO find smarter way of doing this, implement at p-dict level?
  (define ->t (algebra-->t alg))
  (define t= (algebra-t= alg))
  (and (= (poly-degree PA) (poly-degree PB))
       (equal? (poly-vars PA)(poly-vars PB))
       (= ((p-dict-size (poly-coefficients PA))) ((p-dict-size (poly-coefficients PB))))
       (for/and : Boolean
         ([(k v) (in-coefficients PA)])
         (t= (->t v)(->t (poly-coefficient PB k))))
       (for/and : Boolean
         ([(k v) (in-coefficients PB)])
         (t= (->t v)(->t (poly-coefficient PA k))))))

;***********************************************************************************************************************
;* string representation of poly                                                                                       *
;***********************************************************************************************************************
(define #:forall (A B) (poly->string [alg : (Algebra+* A)][P : (Poly (∩ A B))])
  (define zero (algebra-zero alg))
  (define one (algebra-one alg))
  (define vars (poly-vars P))
  (define (make-term [v : A][k : Monomoid-Exponents]) : String
    (cond
      [(equal? v zero) ""]
      [else
       (define b
         (add-between (for/list : (Listof String)
                        ([i k]
                         [x vars]
                         #:unless (= i 0))
                        (format "~a~a" x (if (= i 1) "" (format "^~a" i))))
                      "×"))
       (define b* (if (equal? b '()) (list (format "~a^0" (monomoid-first vars))) b))
       (cond
         [(equal? v one)(format "~a" b*)]
         [else (format "~a×~a" v b*)])]))
  (define S
    (apply
     string-append
     (for/list : (Listof String)
       ([([k : Monomoid-Exponents][v : A]) (in-coefficients P)]
        [i (in-naturals)])
       (define S (make-term v k))
       (cond
         [(equal? S "") S]
         [(= i 0) S]
         [(not (real? v)) (string-append " +"S)]
         [(<= 0 v) (string-append " +" S)]
         [else (string-append " " S)]))))
  (if (string=? S "") (format "~a" zero) S))

;***********************************************************************************************************************
;* map over the poly-coefficients                                                                                      *
;***********************************************************************************************************************

(define #:forall (A B) (poly-1-map [alg : (Algebra+* A)]
                                   [fct : ((List Monomoid-Exponents B) -> (List Monomoid-Exponents A))]
                                   [P : (Poly B)]
                                   [vars* : (Option Monomoid-Base) #f]) : (Poly A)
  (make-poly alg
             (map fct (poly->coefficient-list P))
             (or vars* (poly-vars P))))

(define #:forall (A B C) (poly-2-map [alg : (Algebra+* A)]
                                     [fct : (Monomoid-Exponents
                                             (Option (List Monomoid-Exponents B))
                                             (Option (List Monomoid-Exponents C))
                                             -> (List Monomoid-Exponents A))]
                                     [P1 : (Poly B)]
                                     [P2 : (Poly C)]
                                     [vars* : (Option Monomoid-Base) #f]) : (Poly A)
  (define-values (vars rs) (monomoid-combine (poly-vars P1)(poly-vars P2)))
  (define ks : (HashTable Monomoid-Exponents (Pair (Option Monomoid-Exponents)(Option Monomoid-Exponents)))(make-hash))
  (for ([(k v)(in-coefficients P1)])
    (hash-set! ks ((list-ref rs 0) k) (cons k #f)))
  (for ([(k v)(in-coefficients P2)])
    (hash-update! ks ((list-ref rs 1) k)
                  (λ ([x : (Pair (Option Monomoid-Exponents)(Option Monomoid-Exponents))])
                    (cons (car x) k))
                  (λ () (cons #f #f))))
  (define zero (algebra-zero alg))

  (make-poly alg
             (for/list : (Listof (List Monomoid-Exponents A))
               ([(k v) (in-hash ks)])
               (fct k
                    (if (car v) (list (car v) (poly-coefficient P1 (car v))) #f)
                    (if (cdr v) (list (cdr v) (poly-coefficient P2 (cdr v))) #f)))
             (or vars* vars)))

(define #:forall (A B) (poly-n-map [alg : (Algebra+* A)]
                                   [fct : (Monomoid-Exponents
                                           (Listof (Option (List Monomoid-Exponents B)))
                                           -> (List Monomoid-Exponents A))]
                                   [Ps : (Listof (Poly B))]
                                   [vars* : (Option Monomoid-Base) #f])
  (cond
    [(null? Ps) (make-zero-poly alg vars*)]
    [else
     (define len (length Ps))
     (define zero (algebra-zero alg))

     (define-values (vars remaps)(apply monomoid-combine ((inst map Monomoid-Base (Poly B)) poly-vars Ps)))
     (define ks : (HashTable Monomoid-Exponents (Listof (Option Monomoid-Exponents)))(make-hash))
     (for ([P (in-list Ps)]
           [remap (in-list remaps)]
           [i (in-naturals)])
       (for ([(k v)(in-coefficients P)])
         (hash-update! ks (remap k)
                       (λ ([x : (Listof (Option Monomoid-Exponents))])
                         (list-set x i k))
                       (λ () (make-list len #f)))))

     (make-poly alg
                (for/list : (Listof (List Monomoid-Exponents A))
                  ([(k v) (in-hash ks)])
                  (fct k (for/list : (Listof (Option (List Monomoid-Exponents B)))
                           ([P (in-list Ps)]
                            [expts (in-list v)])
                           (if expts (list expts (poly-coefficient P expts)) #f))))
                (or vars* vars))]))

(define #:forall (A B) (poly-remap [alg : (Algebra+* A)]
                                   [P : (Poly (∩ A B))]
                                   [remap : (-> Monomoid-Exponents Monomoid-Exponents)]
                                   [vars : (Option Monomoid-Base)])
  (poly-1-map alg
              (λ ([a : (List Monomoid-Exponents A)]) : (List Monomoid-Exponents A)
                (cons (remap (car a)) (cdr a)))
              P
              vars))

(define #:forall (A B) (poly-realg [alg : (Algebra+* A)]
                                   [P : (Poly (∩ A B))])
  (make-poly alg (poly->coefficient-list P) (poly-vars P)))

(define #:forall (A) (poly-remove-unused-base-vars [alg : (Algebra+* A)][P : (Poly A)]) : (Poly A)
  (define zero (algebra-zero alg))
  (cond
    [(<= (poly-vars-len P) 1) P]
    [else
     (define l
       (for/fold ([l : (Listof Boolean) (make-list (poly-vars-len P) #f)])
                 ([(k v)(in-coefficients P)]
                  #:break (for/and : Boolean ([li : Boolean (in-list l)])li))
         (if (equal? v zero)
             l
             (for/list ([li (in-list l)]
                        [ki (in-vector k)])
               (or li (< 0 ki))))))
     (cond
       [(for/and : Boolean ([li : Boolean (in-list l)]) li) P]
       [else
        (poly-remap alg
                    P
                    (λ ([e : Monomoid-Exponents]) : Monomoid-Exponents
                      (apply monomoid
                             (for/list : (Listof Nonnegative-Integer)
                               ([li (in-list l)]
                                [ei (in-vector e)]
                                #:when li)
                               ei)))
                    (apply monomoid
                           (for/list : (Listof Symbol)
                             ([li (in-list l)]
                              [bi (in-vector (poly-vars P))]
                              #:when li)
                             bi)))
        P])]))
;***********************************************************************************************************************
;* addition                                                                                                            *
;***********************************************************************************************************************
(define #:forall (A B C) (poly+p [alg : (Algebra+* A)][PA : (Poly (∩ A B))][PB : (Poly (∩ A C))]) : (Poly A)
  (define t+ (algebra-t+ alg))
  (define zero (algebra-zero alg))
  (poly-2-map alg
            (λ ([k : Monomoid-Exponents]
                [a : (Option (List Monomoid-Exponents A))]
                [b : (Option (List Monomoid-Exponents A))])
              (list k (cond
                        [(and a b)(t+ (cadr a)(cadr b))]
                        [a (cadr a)]
                        [b (cadr b)]
                        [else zero])))
            PA PB))

(: poly+ (All (A B ...) (Algebra+* A) (Poly (∩ A B)) ... -> (Poly A)))
(define (poly+ alg . PBs)
  (for/fold ([P (make-zero-poly alg (if (null? PBs) #f (car PBs)))])
            ([Pi (in-list PBs)])
    (poly+p alg P Pi)))

;***********************************************************************************************************************
;* subtraction                                                                                                          *
;***********************************************************************************************************************
(: poly- (All (A B C ...) (Algebra+*- A) (Poly (∩ A B)) (Poly (∩ A C)) ... -> (Poly A)))
(define (poly- alg PA . PBs)
  (define zero (algebra-zero alg))
  (define t- (algebra-t- alg))
  (cond
    [(empty? PBs)
     (poly-1-map alg
                 (λ ([a : (List Monomoid-Exponents A)])
                   (list (car a) (t- zero (cadr a))))
                 PA)]
    [else
     (poly-2-map alg
                 (λ ([k : Monomoid-Exponents]
                     [a : (Option (List Monomoid-Exponents A))]
                     [b : (Option (List Monomoid-Exponents A))])
                   (list k (cond
                             [(and a b)(t- (cadr a)(cadr b))]
                             [a (cadr a)]
                             [b (t- zero (cadr b))]
                             [else zero])))
                 PA (apply (inst poly+ A C ... C) alg PBs))]))


;***********************************************************************************************************************
;* scale                                                                                                               *
;***********************************************************************************************************************
(define #:forall (A B) (poly*s [alg : (Algebra+* A)][PA : (Poly (∩ A B))][s : A]) : (Poly A)
  (define t* (algebra-t* alg))
  (poly-1-map alg (λ ([a : (List Monomoid-Exponents A)])
                    (list (car a) (t* (cadr a) s)))
              PA))

(define #:forall (A B) (poly/s [alg : (Algebra A)][PA : (Poly (∩ A B))][s : A]) : (Poly A)
  (define t/ (algebra-t/ alg))
  (poly-1-map alg
            (λ ([a : (List Monomoid-Exponents A)])
              (list (car a) (t/ (cadr a) s)))
            PA))
(define poly-scale poly*s)

;***********************************************************************************************************************
;* multiplication                                                                                                      *
;***********************************************************************************************************************
(define #:forall (A B) (poly*k-v [alg : (Algebra+* A)][P : (Poly (∩ A B))][k : Monomoid-Exponents][v : A]) : (Poly A)
  (define t* (algebra-t* alg))
  (poly-1-map alg
              (λ ([a : (List Monomoid-Exponents A)])
                (list (monomoid-exponents* (car a) k )(t* (cadr a) v)))
              P))

(define #:forall (A B C) (poly*p [alg : (Algebra+* A)][PA : (Poly (∩ A B))][PB : (Poly (∩ A C))]) : (Poly A)
  (define t+ (algebra-t+ alg))
  (define t* (algebra-t* alg))
  (define-values (vars remaps)(monomoid-combine (poly-vars PA)(poly-vars PB)))
  (define P0 ((inst poly-remap A B) alg PA (list-ref remaps 0) vars))
  (define P1 ((inst poly-remap A C) alg PB (list-ref remaps 1) vars))
  
  (for/fold : (Poly A)
   ([P (make-zero-poly alg vars)])
   ([(k v) (in-coefficients P1)])
    (poly+p alg P (poly*k-v alg P0 k v))))

(define #:forall (A B C ...) (poly* [alg : (Algebra+* A)] . [PBs : (Poly (∩ A C)) ... C]) : (Poly A)
  (for/fold ([P (make-one-poly alg (if (null? PBs) #f (car PBs)))])
            ([Pi (in-list PBs)])
    (poly*p alg P Pi)))

;***********************************************************************************************************************
;* exponentiation                                                                                                      *
;***********************************************************************************************************************
(: poly-expt (All (A B) ((Algebra+* A) (Poly (∩ A B)) Nonnegative-Integer -> (Poly A))))
(define (poly-expt alg P e)
  (cond
    [(= 0 e) (make-one-poly alg P)]
    [(= 1 e) ((inst poly-realg A B) alg P)]
    [(= 2 e) ((inst poly*p A B B) alg P P)]
    [else
     (define n/2 (/ e 2))
     (cond
       [(integer? n/2)
        (define P^2 ((inst poly*p A B B) alg P P))
        (poly-expt alg P^2 n/2)]
       [else
        ((inst poly*p A B A) alg P ((inst poly-expt A B) alg P (- e 1)))])]))

;***********************************************************************************************************************
;* division                                                                                                            *
;***********************************************************************************************************************
;TODO switch from long division to synthetic division
(: poly-quotient/remainder (All (A B C) ((Algebra A)(Poly (∩ A B))(Poly (∩ A C)) -> (Values (Poly A) (Poly A)))))
(define (poly-quotient/remainder alg PA PB)
  (unless (= 1 (poly-vars-len PA)(poly-vars-len PB))
    (error "poly-quotient/remainder: not (yet) implemented for multivariable polynomials"
           (poly-vars PA) (poly-vars PB)))
  (define vars (poly-vars PB))
  (define R ((inst poly-realg A B) alg PA))
  (cond
    [(equal? (poly-vars PA) vars)
     (define d (poly-degree PB))
     (define b_n (poly-coefficient PB (monomoid d)))
     (define t/ (algebra-t/ alg))
     (let loop ([Q (make-zero-poly alg vars)]
                [R R])
       (define dR (poly-degree R))
       (define d* (- dR d))
       (cond
         [(< d* 0)(values Q R)]
         [else
          (define rn (t/ (poly-coefficient R (monomoid dR)) b_n))
          (loop (poly+p alg Q (make-sparse-poly alg (list (list (monomoid d*) rn)) vars))
                (poly- alg R ((inst poly*k-v A C) alg PB (monomoid d*) rn)))]))]
    [else (values (make-zero-poly alg vars)
                  R)]))

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
(: poly-substitute (All (A B C) ((Algebra+* B)(Poly A) Symbol (Poly (∩ B C)) -> (Poly B))))
(define (poly-substitute alg PA var PB)
  (define ->t (algebra-->t alg))
  (define-values (vars nr remapA remapB)(monomoid-substitute (poly-vars PA) var (poly-vars PB)))
  (define PB* ((inst poly-remap B C) alg PB remapB vars))
  (define get-exp (exp-hash (make-one-poly alg PB*)
                            PB*
                            (λ ([P1 : (Poly B)][P2 : (Poly B)]) : (Poly B)
                              (poly*p alg P1 P2))))
  (for/fold : (Poly B)
    ([P (make-zero-poly alg PB*)])
    ([(k v)(in-coefficients PA)])
    (define e (monomoid-ref k nr))
    (poly+p alg
            P
            (poly*k-v alg
                      (get-exp e)
                      (remapA k)
                      (->t v)))))

;***********************************************************************************************************************
;* evaluate                                                                                                            *
;***********************************************************************************************************************
(: poly-evaluate (All (A B) ((Algebra+* A)(Poly (∩ A B)) A * -> A)))
(define (poly-evaluate alg P . xs)
  (unless (equal? (poly-vars-len P)(length xs))
    (raise-argument-error 'poly-evaluate "Coefficients don't map" (list (poly-vars P) '-> xs)))
  (define zero (algebra-zero alg))
  (define one (algebra-one alg))
  (define t+ (algebra-t+ alg))
  (define t* (algebra-t* alg))
  (define exps (map (λ ([x : A])(exp-hash one x t*)) xs))
  (define (× [v1 : A][vs : Monomoid-Exponents]) : A
    (for/fold ([S v1])
              ([v : Nonnegative-Integer vs]
               [e exps])
      (t* S (e v))))
  (for/fold : A
    ([S zero])
    ([(k v)(in-coefficients P)])
    (t+ S (× v k))))

;***********************************************************************************************************************
;* differentiate                                                                                                       *
;***********************************************************************************************************************
(define #:forall (A B) (poly-diff [alg : (Algebra+* A)]
                                  [P : (Poly (∩ A B))]
                                  [n : Nonnegative-Integer 1]
                                  [x : Symbol 'x]
                                  ) : (Poly A)
  (define d (poly-degree P))
  (define d* (- d n))
  (define i (monomoid-has? (poly-vars P) x))
  (define ->t (algebra-->t alg))
  (define t* (algebra-t* alg))
  (cond
    [(< d* 0) (make-zero-poly alg P)]
    [(not i) (make-zero-poly alg P)]
    [(= n 0) ((inst poly-realg A B) alg P)]
    [else
     (make-poly alg
                (for*/list : (Listof (List Monomoid-Exponents A))
                  ([(k v) (in-coefficients P)]
                   [e (in-value (monomoid-ref k i))]
                   [e+ (in-value (- e n))]
                   #:when (<= 0 e+))
                  (define factor (for/fold : Integer ([f 1])([i (in-range e e+ -1)]) (* f i)))
                  (list (list->monomoid (list-set (monomoid->list k) i e+))
                        (t* (->t factor) v)))
                (poly-vars P))]))

;***********************************************************************************************************************
;* integrate                                                                                                           *
;***********************************************************************************************************************
(define #:forall (A B) (poly-int [alg : (Algebra A)]
                                 [P : (Poly (∩ A B))]
                                 [n : Nonnegative-Integer 1]
                                 [x : Symbol 'x]
                                 ) : (Poly A)
  (define (getfactor [e+ : Nonnegative-Integer][e : Nonnegative-Integer])
    (for/fold : Integer ([f 1])([i (in-range e+ e -1)]) (* f i)))
  (define i (monomoid-has? (poly-vars P) x))
  (define ->t (algebra-->t alg))
  (define t/ (algebra-t/ alg))
  (cond
    [(not i) ((inst poly*p A A B) alg
                     (make-poly alg `(((,n) ,(->t (getfactor n 0)))) (monomoid x))
                     P)]
    [(= n 0) ((inst poly-realg A B) alg P)]
    [else
     (make-poly alg
                (for*/list : (Listof (List Monomoid-Exponents A))
                  ([(k v) (in-coefficients P)]
                   [e (in-value (monomoid-ref k i))]
                   [e+ (in-value (+ e n))]
                   #:when (<= 0 e+))
                  (list (list->monomoid (list-set (monomoid->list k) i e+))
                        (t/ (->t (getfactor e+ e)) v)))
                (poly-vars P))]))

;***********************************************************************************************************************
;* construct from roots                                                                                                *
;***********************************************************************************************************************
(: poly-from-roots (All (A B) (case-> ((Algebra+*- A) (Listof A) -> (Poly A))
                                      ((Algebra+*- A) (Listof A) (Algebra+* B) -> (Poly B)))))
(define poly-from-roots
  (case-lambda
   [(alg lst)
    (define zero (algebra-zero alg))
    (define one (algebra-one alg))
    (define t- (algebra-t- alg))
    (for/fold ([P (make-one-poly alg)])
              ([r (in-list lst)])
      (poly* alg P (make-poly alg `(((1) ,one)((0),(t- zero r))))))]
   [(alg lst alg2)
    (define ->t (algebra-->t alg2))
    (poly-1-map
     alg2 (λ ([k : (List Monomoid-Exponents A)])
            (list (car k) (->t (cadr k))))
     ((inst poly-from-roots A) alg lst))]))

;***********************************************************************************************************************
;* TODO abs coefficients                                                                                               *
;***********************************************************************************************************************

;***********************************************************************************************************************
;* easy syntax                                                                                                         *
;***********************************************************************************************************************
(define-syntax (with-algebra stx)
  (syntax-case stx (:)
    [(_ [alg : A] body ...)
     (with-syntax ([make (format-id stx "make-poly")]
                   [string (format-id stx "poly->string")]
                   [sum (format-id stx "poly+")]
                   [prod (format-id stx "poly*")]
                   [scale (format-id stx "poly-scale")]
                   [sub (format-id stx "poly-")]
                   [div (format-id stx "poly-quotient/remainder")]
                   [expt (format-id stx "poly-expt")]
                   [subst (format-id stx "poly-substitute")]
                   [diff (format-id stx "poly-diff")]
                   [int (format-id stx "poly-int")])
       #'(let ([make (λ ([p : (Cofs A)][v : (Option Monomoid-Base) #f])(make-poly alg p v))]
               [string (λ ([P : (Poly A)])(poly->string alg P))]
               [sum (λ ([P : (Poly A)].[Ps : (Poly A) *])(apply poly+ alg P Ps))]
               [sub (λ ([P : (Poly A)].[Ps : (Poly A) *])(apply poly- alg P Ps))]
               [scale (λ ([P : (Poly A)][e : A])(poly-scale alg P e))]
               [prod (λ ([P : (Poly A)].[Ps : (Poly A) *])(apply poly* alg P Ps))]
               [div (λ ([PA : (Poly A)][PB : (Poly A)])(poly-quotient/remainder alg PA PB))]
               [expt (λ ([P : (Poly A)][e : Nonnegative-Integer])(poly-expt alg P e))]
               [subst (λ #:forall (B)([PB : (Poly B)][x : Symbol][PA : (Poly A)]) (poly-substitute alg PB x PA))]
               [diff (λ ([P : (Poly A)][n : Nonnegative-Integer 1][x : Symbol 'x])(poly-diff alg P n x))]
               [int  (λ ([P : (Poly A)][n : Nonnegative-Integer 1][x : Symbol 'x])(poly-int  alg P n x))])
           body ...))]))

(module+ test0
  (with-algebra [C-algebra : Number]
    (define (printit [str : String][P : (Poly Number)])
      (printf "~a: <d~a - ~a> ~a\n\n" str (poly-degree P)(poly-vars P)(poly->string P)))
    
    (define P0 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 3 2) 1)(list (monomoid 2 0) 3))
                          (monomoid 'x 'y)))
    (define P1 (make-poly (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 4 2) 1))
                          (monomoid 'z 'x)))
    (poly-degree P0)
    (printit "P0" P0)
    (poly-degree P1)
    (printit "P1" P1)

    (define P2 (poly+ P0 P1))
    
    (printit "P0+P1" P2)

    (define P3 (poly-scale P0 2))
    (printit "P0*2" P3)

    (define P4 (poly* P0 P1))
    (printit "P0*P1" P4)
    ))

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
  (define #:forall (A) (printit [str : String][alg : (Algebra A)][P : (Poly A)])
      (printf "~a: <d~a - ~a> ~a\n\n" str (poly-degree P)(poly-vars P)(poly->string alg P)))
  (: Cpoly/ascending (->* [][#:base Symbol] #:rest Number (Poly Number)))
  (define (Cpoly/ascending #:base [var 'x] . vs)
    (make-dense-poly algebra-C
                     (for/list : (Listof (List Monomoid-Exponents Number))
                       ([v (in-list vs)]
                        [i : Nonnegative-Integer (in-naturals)])
                       (list (monomoid i) v))
                     (monomoid var)))

  ;my favorite shorthand
  (: Cpoly/descending (->* [][#:base Symbol] #:rest Number (Poly Number)))
  (define (Cpoly/descending #:base [var 'x] . vs)
    (make-dense-poly algebra-C
                     (for/list : (Listof (List Monomoid-Exponents Number))
                       ([v (in-list (reverse vs))]
                        [i : Nonnegative-Integer (in-naturals)])
                       (list (monomoid i) v))
                     (monomoid var)))

  (printf "Defining and printing some polynomials in Bool\n----------------------------------------------\n")
  (define bP0 (make-poly algebra-Bool '(((3) #t)((0)#t))))
  (printit "bP0" algebra-Bool bP0)
  (define bP1 (make-poly algebra-Bool '(((1 1)#t)((2 0)#t)) (monomoid 'x 'y)))
  (printit "bP1" algebra-Bool bP1)

  (printit "bP0+bP1" algebra-Bool (poly+ algebra-Bool bP0 bP1))
  
  (printit "bP0*bP1" algebra-Bool (poly* algebra-Bool bP0 bP1))
  (printit "bP1^2  " algebra-Bool (poly-expt algebra-Bool bP1 2))

  (printf "\nNow in ℂ\n--------\n")
  (define P0 (make-poly algebra-C
                        (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 3 2) 1)(list (monomoid 2 0) 3))
                        (monomoid 'x 'y)))
  (printit "P0" algebra-C P0)
  (define P1 (make-poly algebra-C
                        (list (list (monomoid 1 1) -1.0)(list (monomoid 0 2) 1)(list (monomoid 4 2) 1))
                        (monomoid 'z 'x)))
  (printit "P1" algebra-C P1)
  (define P2 (make-poly algebra-C '(((1 3) 1)((1 0)1)((0 0)1)) (monomoid 'x 'y)))
  (printit "P2" algebra-C P2)
  (define P3 (Cpoly/descending #:base 'y 2 0 1))
  (printit "P3" algebra-C P3)

  (printit "P0+P1" algebra-C (poly+ algebra-C P0 P1))
  (printit "P1*P2" algebra-C (poly* algebra-C P1 P2))
  (printit "P3^2 " algebra-C (poly-expt algebra-C P3 2))

  (printf "P2(1.2 3i)=~a\n" (poly-evaluate algebra-C P2 1.2 +3i))

  (printf "\nSubstitute y in P2 by the boolean polynomial bP1\n")
  (printit "(poly-substitute P2 'y bP1)" algebra-Bool (poly-substitute algebra-Bool P2 'y bP1))

  (printf "(the other way around would not work, since the operations over ℂ don't\n  know how to convert a Boolean to a Number\n  Notice that ->Bool is taking any value other than 0 or #f as #t)\n")

  (printf "\nDivision in C\n-------------\n")
  (define S1 (make-poly C-algebra'(((5) 1)((0) 1))))
  (printit "S1" C-algebra S1)
  (define S2 (make-poly C-algebra '(((1) 1)((0) -1))))
  (printit "S2" C-algebra S2)

  (define-values (Q R)
    (poly-quotient/remainder C-algebra S1 S2))
  (printit "Q(S1/S2)" C-algebra Q)
  (printit "R(S1/S2)" C-algebra R)
  (printit "Q(S1/S2)*S2" C-algebra (poly+ C-algebra R (poly* C-algebra Q S2)))

  (define S4 (make-poly C-algebra '(((1) 1)((0) 1))))
  (printit "S4" C-algebra S4)
  (define-values (Q2 R2)
    (poly-quotient/remainder C-algebra S1 S4))
  (printit "Q(S1/S4)" C-algebra Q2)
  (printit "R(S1/S4)" C-algebra R2)
  (printit "R(S1/S4)+(Q(S1/S4)*S4)" C-algebra (poly+ C-algebra R2 (poly* C-algebra Q2 S4)))
  
  (define S5 (make-poly C-algebra '(((1) 4)((2) 3))))
  (printit "S5" C-algebra S5)
  (define-values (Q3 R3)
    (poly-quotient/remainder C-algebra S1 S5))
  (printit "Q(S1/S5)" C-algebra Q3)
  (printit "R(S1/S5)" C-algebra R3)
  (printit "R(S1/S5)+(Q(S1/S5)*S5)" C-algebra (poly+ C-algebra R3 (poly* C-algebra Q3 S5)))
  )