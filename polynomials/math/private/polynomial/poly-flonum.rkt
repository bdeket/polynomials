#lang typed/racket/base

(require math/flonum
         racket/vector)
(provide (except-out (all-defined-out) make-flpoly))

(module+ test
  (require typed/rackunit))

;flpoly is vector with coefficients going from small to large
;a0+a1.x+a2.x²+...+an.x^n -> (flpoly #(a0 a1 a2 ... an) n)

(struct flpoly ([v : (Vectorof Flonum)][degree : Nonnegative-Integer])
  #:transparent
  #:constructor-name make-flpoly)

;------------------------------------
;construction and accessors
;------------------------------------
(define (const-flpoly [ai : Flonum]) (make-flpoly (vector ai) 0))
(define flpoly-zero (const-flpoly 0.0))
(define flpoly-one (const-flpoly 1.0))
(define (flpoly-copy [P : flpoly])(make-flpoly (vector-copy (flpoly-v P)) (flpoly-degree P)))

(define (flpolyV< [v : (Vectorof Flonum)]) : flpoly
  (define L (vector-length v))
  (cond
    [(equal? v #()) (raise-argument-error 'flpolyV< "Empty coefficients" v)]
    [else
     (define n : (Option Nonnegative-Integer)
       (let loop ([i (- L 1)])
         (cond
           [(< i 0) #f]
           [(fl= (vector-ref v i) 0.0) (loop (- i 1))]
           [else i])))
     (if n
         (let ([L* (+ n 1)])(make-flpoly (if (= L L*) v (vector-take v L*)) n))
         flpoly-zero)]))
(define (flpolyL< [a : (Listof Flonum)]) : flpoly (flpolyV< (list->vector a)))
(define (flpoly< [a : (U (Vectorof Flonum)(Listof Flonum)Flonum)] . [b : Flonum *]) : flpoly
  (cond
    [(or (vector? a)(list? a))
     (unless (null? b)
       (raise-argument-error 'flpoly< "rest arguments empty if first is vector/list" 2 a b))
     (if (vector? a)(flpolyV< a)(flpolyL< a))]
    [else (flpolyV< (list->vector (cons a b)))]))

(define (flpolyV> [v : (Vectorof Flonum)]) : flpoly
  (cond
    [(equal? v #()) (raise-argument-error 'flpolyV< "Empty coefficients" v)]
    [else
     (define n : (Option Nonnegative-Integer)
       (for/or ([ai : Flonum (in-vector v)]
                [i : Nonnegative-Integer (in-naturals)])
         (if (fl= ai 0.0) #f i)))
     (define d (if n (- (vector-length v) n 1) -1))
     (if (and n (<= 0 d))
         (make-flpoly (for/vector : (Vectorof Flonum)
                        ([ai ((inst in-vector Flonum) v (- (vector-length v) 1) (- n 1) -1)])
                        ai)
                      d)
         flpoly-zero)]))
(define (flpolyL> [a : (Listof Flonum)]) : flpoly (flpolyV> (list->vector a)))
(define (flpoly> [a : (U (Vectorof Flonum)(Listof Flonum)Flonum)] . [b : Flonum *]) : flpoly
  (cond
    [(or (vector? a)(list? a))
     (unless (null? b)
       (raise-argument-error 'flpoly< "rest arguments empty if first is vector/list" 2 a b))
     (if (vector? a)(flpolyV> a)(flpolyL> a))]
    [else (flpolyV> (list->vector (cons a b)))]))

(: flpoly-from-roots (->* () (#:s Flonum) #:rest Number flpoly))
(define (flpoly-from-roots #:s [s 1.0] . rs)
  (define Ss
    (let loop : (Listof flpoly)([rs : (Listof Number) rs])
      (cond
        [(null? rs) '()]
        [(real? (car rs))
         (cons (make-flpoly (vector (- (fl (car rs))) 1.0) 1)
               (loop (cdr rs)))]
        [else
         (define z (car rs))
         (define zr (real-part z))
         (define zi (imag-part z))
         (define z* (- zr (* +i zi)))
         (unless (member z* (cdr rs)) (raise-argument-error 'flpoly-from-roots (format "complex conjugate pair (~a ~a)" z z*) z))
         (cons (make-flpoly (vector (fl (+ (* zr zr)(* zi zi))) (fl (* 2 zr)) 1.0) 2)
               (loop (remove z* (cdr rs))))])))
  (apply flpoly*-accurate
         (make-flpoly (vector s) 0)
         Ss))

(define (flpoly-coefficient [P : flpoly] [n : Integer]) : Flonum
  (cond
    [(<= 0 n (flpoly-degree P))(vector-ref (flpoly-v P) n)]
    [else 0.0]))
(define (flpoly-reverse-coefficient [P : flpoly] [n : Integer]) : Flonum
  (flpoly-coefficient P (- (flpoly-degree P) n)))
(module+ test
  (check-equal? (flpoly> 0.0 1.1 2.2 3.3) (flpoly< 3.3 2.2 1.1 0.0))
  (check-equal? (flpoly-degree (flpoly> 0.0 1.1 2.2 3.3)) 2)
  (check-equal? (flpoly-coefficient (flpoly> 3.3 2.2 1.1 0.0) 2) 2.2)
  (check-equal? (flpoly-coefficient (flpoly< 0.0 1.1 2.2 3.3) 2) 2.2)
  (check-equal? (flpoly-coefficient (flpoly< 0.0 1.1 2.2 3.3) 8) 0.0)
  (check-equal? (flpoly-reverse-coefficient (flpoly> 3.3 2.2 1.1 0.0) 2) 1.1)
  (check-equal? (flpoly-reverse-coefficient (flpoly< 0.0 1.1 2.2 3.3) 2) 1.1)
  (check-equal? (flpoly-reverse-coefficient (flpoly< 0.0 1.1 2.2 3.3) 8) 0.0)
  (check-equal? (flpoly> 0.0 0.0 0.0 1.1 0.1) (make-flpoly #(0.1 1.1) 1))
  (check-equal? (flpoly-from-roots 1.0 1.0 1.0 1.0) (flpoly> 1.0 -4.0 6.0 -4.0 1.0)))

;------------------------------------
;evaluating the poly
;------------------------------------
(define-type flPevaluator (-> flpoly Flonum Flonum))
(define-type cPevaluator (case-> (-> flpoly Flonum Flonum)
                                 (-> flpoly Number Number)))

(: Horner flPevaluator)
(define (Horner P t)
  (for/fold : Flonum
    ([sum : Flonum 0.0])
    ([ai ((inst in-vector Flonum) (flpoly-v P) (flpoly-degree P) -1 -1)])
    (fl+ (fl* sum t) ai)))

(: complexHorner cPevaluator)
(define (complexHorner P z)
  (cond
    [(flonum? z)(Horner P z)]
    [else
     (for/fold : Number
       ([sum : Number 0])
       ([ai ((inst in-vector Flonum) (flpoly-v P) (flpoly-degree P) -1 -1)])
       (+ (* sum z) ai))]))

(: Horner+ flPevaluator)
(define (Horner+ P t)
  (let loop ([i : Nonnegative-Integer 0]
             [x : Flonum 1.0]
             [ans : (Listof Flonum) '()])
    (cond
      [(< (flpoly-degree P) i) (flsum ans)]
      [else (loop (+ i 1) (* x t) (cons (* x (flpoly-coefficient P i)) ans))])))


(define (hornerEFT [P : flpoly] [t : Flonum]) : (Values Flonum flpoly flpoly)
  (define-values (ans pπ pσ)
    (for/fold : (Values Flonum (Listof Flonum) (Listof Flonum))
      ([ans : Flonum (flpoly-reverse-coefficient P 0)]
       [pπ : (Listof Flonum) '()]
       [pσ : (Listof Flonum) '()])
      ([ai : Flonum ((inst in-vector Flonum) (flpoly-v P) (- (flpoly-degree P) 1) -1 -1)])
      (define-values (pi πi)(fl*/error ans t))
      (define-values (si σi)(fl+/error pi ai))
      (values si (cons πi pπ)(cons σi pσ))))
  (values ans
          (flpolyL< pπ)
          (flpolyL< pσ)))
(define (hornerSum [P1 : flpoly] [P2 : flpoly] [t : Flonum]) : Flonum
  (for/fold ([ans 0.0])
            ([ai ((inst in-vector Flonum) (flpoly-v P1) (flpoly-degree P1) -1 -1)]
             [bi ((inst in-vector Flonum) (flpoly-v P2) (flpoly-degree P2) -1 -1)])
    (fl+ (fl* ans t) (fl+ ai bi))))
(: compensatedHorner flPevaluator)
(define (compensatedHorner P t)
  (cond
    [(or (fl= t 0.0)(= (flpoly-degree P) 0))
     (flpoly-coefficient P 0)]
    [else
     (define-values (h pπ pσ)(hornerEFT P t))
     (fl+ h (hornerSum pπ pσ t))]))

(module+ test
  (check-equal? (compensatedHorner (flpoly> 1.0 2.0 1.0) 0.0) 1.0)
  (check-equal? (compensatedHorner (flpoly> 1.0 2.0 1.0) 1.0) 4.0)
  (check-equal? (compensatedHorner (flpoly> 1.0 2.0 1.0) 1.0) 4.0)
  (let ([P (flpoly> 1.0 1.0 0.0 0.0 3.0 1.0)])
    (check-equal? (compensatedHorner P 0.0) (Horner P 0.0))
    (check-equal? (compensatedHorner P 1.0) (Horner P 1.0)))
  (check-equal? (complexHorner (flpoly> 1.0 2.0 1.0) +i) 0.0+2.0i))

;------------------------------------
;basic operations +-*^Scale
;------------------------------------
(define (flpoly+p [P1 : flpoly] [P2 : flpoly]) : flpoly
  (define v (vector-copy(if (< (flpoly-degree P1)(flpoly-degree P2))
                            (flpoly-v P2)
                            (flpoly-v P1))))
  (for ([ai (in-vector (flpoly-v P1))]
        [bi (in-vector (flpoly-v P2))]
        [i (in-naturals)])
    (vector-set! v i (fl+ ai bi)))
  (flpolyV< v))

(define (flpoly+ [Pf : flpoly]. [Pr : flpoly *]) : flpoly
  (define Ps (cons Pf Pr))
  (define d (apply max (map flpoly-degree Ps)))
  (define v (for/vector : (Vectorof Flonum)
              ([i (in-range (+ d 1))])
              (flsum (map (λ ([P : flpoly])(flpoly-coefficient P i)) Ps))))
  (flpolyV< v))

(module+ test
  (check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> 2.0 8.0)) (flpoly> 4.0 5.0 10.0))
  (check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> -4.0 2.0 8.0)) (flpoly> 5.0 10.0))
  (check-equal? (flpoly+p (flpoly> 4.0 3.0 2.0) (flpoly> -4.0 -3.0 -2.0)) flpoly-zero)
  (check-equal? (flpoly+ (flpoly< 1.0 0.0) (flpoly< 1e-16 0.0)(flpoly< 1e-16 0.0)) (flpoly< 1.0000000000000002 0.0)))

(define (flpoly-p [P1 : flpoly] [P2 : flpoly]) : flpoly
  (define d (max (flpoly-degree P1)(flpoly-degree P2)))
  (define v (vector-copy(if (< (flpoly-degree P1)(flpoly-degree P2))
                            (flpoly-v P2)
                            (flpoly-v P1))))
  (for ([i (in-range (+ d 1))])
    (vector-set! v i (fl- (flpoly-coefficient P1 i)(flpoly-coefficient P2 i))))
  (flpolyV< v))

(define (flpoly- [Pf : flpoly] . [Pr : flpoly *]) : flpoly
  (define P- (flpoly*s Pf -1.0))
  (cond
    [(null? Pr) P-]
    [else (flpoly*s (apply flpoly+ P- Pr) -1.0)]))

(module+ test
  (check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 2.0 8.0)) (flpoly> 4.0 1.0 -6.0))
  (check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 4.0 2.0 8.0)) (flpoly> 1.0 -6.0))
  (check-equal? (flpoly-p (flpoly> 4.0 3.0 2.0) (flpoly> 4.0 3.0 2.0)) flpoly-zero)
  (check-equal? (flpoly- (flpoly< 1e-16)(flpoly< -1.0)(flpoly< -1e-16)) (flpoly> 1.0000000000000002)))


(define (flpoly*s [P : flpoly] [s : Flonum]) : flpoly
  (cond
    [(= s 0.0)(make-flpoly (vector s) 0)]
    [else (make-flpoly (for/vector : (Vectorof Flonum)
                         ([ai (in-vector (flpoly-v P))])
                         (fl* ai s))
                       (flpoly-degree P))]))
(module+ test
  (check-equal? (flpoly*s (flpoly> 4.0 3.0 2.0) 2.0) (flpoly> 8.0 6.0 4.0)))

(define (flpoly*p [P1 : flpoly] [P2 : flpoly]) : flpoly
  (define d (+ (flpoly-degree P1)(flpoly-degree P2)))
  (define v 
    (for/vector : (Vectorof Flonum)
      ([i : Nonnegative-Integer (in-range (+ d 1))])
      (flsum
       (for*/list : (Listof Flonum)
         ([k  (in-range (+ i 1))]
          [l  (in-value (- i k))]);<=why can't this typecheck as Nonnegative-Integer :(
         (fl* (flpoly-coefficient P1 k)
              (flpoly-coefficient P2 l))))))
  (make-flpoly v d))
;next-one looks nice but is a factor 3 slower :(
#;(define (flpoly*p [P1 : flpoly] [P2 : flpoly]) : flpoly
  (for/fold ([v flpoly-zero])
            ([ai (in-vector (flpoly-v P1))]
             [i (in-naturals)])
    (flpoly+ v (flpoly*s (flpoly-shift P2 i) ai))))

;calculates (flpoly*  (flpoly> 1.0 1.0)(flpoly> 1.0 1e-16)(flpoly> 1.0 1e-12)(flpoly> 1.0 1e-13)(flpoly> 1.0 1e-16))
;with less error creep, but around t² times slower than the next algorithm...
(define (flpoly*-accurate [Pf : flpoly]. [Pr : flpoly *]) : flpoly
  (define N (+ (length Pr) 1))
  (define Ps (cons Pf Pr))
  (define d (apply + (map flpoly-degree Ps)))
  (define dm (apply max (map flpoly-degree Ps)))
  (define H : (HashTable (Pair Integer Integer) (Listof Flonum)) (make-hash))
  (define (getcof [Ps : (Listof flpoly)]
                  [n : Positive-Integer]
                  [i : Nonnegative-Integer]) : (Listof Flonum)
    (cond
      [(hash-ref H (cons n i) (λ () #f))]
      [else
       (define n-1 (- n 1))
       (define ans
         (cond
           [(= n-1 0) (list (flpoly-coefficient (car Ps) i))]
           [(< (* dm n) i) '()]
           [else
            (apply
             append
             (for/list : (Listof (Listof Flonum))
               ([j : Nonnegative-Integer (in-range (+ i 1))])
               (define c (flpoly-coefficient (car Ps) (- i j)));<=why can't (- i j) typecheck as Nonnegative-Integer :(
               (if (fl= c 0.0)
                   '()
                   (map (λ ([x : Flonum]) (* c x))
                        (getcof (cdr Ps) n-1 j)))))]));<=why can't (- n 1) typecheck as Nonnegative-Integer :(
       (hash-set! H (cons n i) ans)
       ans]))
  (define v
    (for/vector : (Vectorof Flonum)
      ([i : Nonnegative-Integer (in-range (+ d 1))])
      (flsum (getcof Ps N i))))
  (make-flpoly v d))
(define (flpoly* [Pf : flpoly]. [Pr : flpoly *]) : flpoly
  (cond
    [(null? Pr) (flpoly-copy Pf)]
    [else (apply flpoly* (flpoly*p Pf (car Pr)) (cdr Pr))]))

(module+ test
  (check-equal? (flpoly*p (flpoly> 4.0 1.0)(flpoly> 2.0 2.0)) (flpoly> 8.0 10.0 2.0))
  (check-equal? (flpoly*-accurate  (flpoly> 4.0 1.0)(flpoly> 2.0 2.0)) (flpoly> 8.0 10.0 2.0))
  (check-equal? (flpoly*p (flpoly> 1.0 1.0)(flpoly*p (flpoly> 1.0 1.0)(flpoly> 1.0 1.0))) (flpoly> 1.0 3.0 3.0 1.0))
  (check-equal? (flpoly*-accurate  (flpoly> 1.0 1.0)(flpoly> 1.0 1.0)(flpoly> 1.0 1.0)) (flpoly> 1.0 3.0 3.0 1.0))
  (check-equal? (flpoly*-accurate  (flpoly> 4.0 8.0 1.0)(flpoly> 2.0 2.0 .5 .4))
                (flpoly*p (flpoly> 4.0 8.0 1.0)(flpoly> 2.0 2.0 .5 .4))))

;------------------------------------
;expt and subst shift reverse
;------------------------------------
;TODO:eliminate errorcreep as with *-accurate?
;do it via binomial?
(define (flpoly-expt [P : flpoly] [n : Nonnegative-Integer]) : flpoly
  (cond
    [(= n 0) flpoly-one]
    [(= n 1) (flpoly-copy P)]
    [(let ([n/2 (/ n 2)])(if (integer? n/2) n/2 #f))
     =>
     (λ(n/2)(let ([Pi (flpoly-expt P n/2)])(flpoly*p Pi Pi)))]
    [else (flpoly*p P (flpoly-expt P (- n 1)))]))
(module+ test
  (check-equal? (flpoly-expt (flpoly> 1.0 2.0) 0) flpoly-one)
  (check-equal? (flpoly-expt (flpoly> 1.0 2.0) 1) (flpoly> 1.0 2.0))
  (check-equal? (flpoly-expt (flpoly> 1.0 2.0) 2) (flpoly> 1.0 4.0 4.0))
  (check-equal? (flpoly-expt (flpoly> 1.0 1.0) 5) (flpoly> 1.0 5.0 10.0 10.0 5.0 1.0)))

;TODO:eliminate errorcreep?
(define (flpoly-subst [P : flpoly] [x : flpoly]) : flpoly
  (define-values (sum x^n+1)
    (for/fold : (Values (Listof flpoly) flpoly)
      ([sum : (Listof flpoly) '()]
       [x^i-1 : flpoly flpoly-one])
      ([i : Nonnegative-Integer (in-range 1 (+ (flpoly-degree P) 1))])
      (define x^i (flpoly*p x^i-1 x))
      (values (cons (flpoly*s x^i (flpoly-coefficient P i)) sum)
              x^i)))
  (apply flpoly+ (const-flpoly (flpoly-coefficient P 0)) sum))
(module+ test
  (check-equal? (flpoly-subst (flpoly> 1.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 2.0 1.0))
  (check-equal? (flpoly-subst (flpoly> 1.0 0.0 0.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 4.0 6.0 4.0 1.0))
  (check-equal? (flpoly-subst (flpoly> 1.0 0.0 2.0 0.0 0.0) (flpoly> 1.0 1.0)) (flpoly> 1.0 4.0 8.0 8.0 3.0)))

(define (flpoly-shift [P : flpoly] [n : Integer]) : flpoly
  (define d (flpoly-degree P))
  (cond
      [(= n 0) (flpoly-copy P)]
      [(< 0 n) (make-flpoly (vector-append (make-vector n 0.0) (flpoly-v P)) (+ d n))]
      [else
       (define d* (+ d n))
       (if (< d* 0)
           (make-flpoly (vector 0.0) 0)
           (make-flpoly (vector-drop (flpoly-v P) (abs n)) d*))]))
(module+ test
  (check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) 0) (flpoly> 4.0 3.0 2.0))
  (check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) 2) (flpoly> 4.0 3.0 2.0 0.0 0.0))
  (check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) -2) (flpoly> 4.0))
  (check-equal? (flpoly-shift (flpoly> 4.0 3.0 2.0) -3) (flpoly> 0.0)))

(define (flpoly-reverse [P : flpoly][n : Nonnegative-Integer (flpoly-degree P)]) : flpoly
  ((if (= (flpoly-degree P) n)
       values
       (λ ([P : flpoly])
         (flpoly-shift P (- n (flpoly-degree P)))))
   (flpolyV> (flpoly-v P))))
(module+ test
  (check-equal? (flpoly-reverse (flpoly> 3.0 2.0 1.0)) (flpoly> 1.0 2.0 3.0))
  (check-equal? (flpoly-reverse (flpoly> 3.0 2.0 1.0 0.0)) (flpoly> 0.0 1.0 2.0 3.0))
  (check-equal? (flpoly-reverse (flpoly-reverse (flpoly> 3.0 2.0 1.0 0.0))) (flpoly> 3.0 2.0 1.0))
  (check-equal? (flpoly-reverse (flpoly-reverse (flpoly> 3.0 2.0 1.0 0.0)) 3) (flpoly> 3.0 2.0 1.0 0.0)))

;------------------------------------
;diff and int
;------------------------------------
(define (flpoly-diff [P : flpoly] [n : Nonnegative-Integer 1]) : flpoly
  (define d (flpoly-degree P))
  (define d* (- d n))
  (cond
    [(< d* 0) flpoly-zero]
    [(= n 0) (flpoly-copy P)]
    [else
     (define (inner [V : (Vectorof Flonum)] [n : Nonnegative-Integer]) : (Vectorof Flonum)
       (cond
         [(= n 0) V]
         [else
          (inner
           (for/vector : (Vectorof Flonum)
             ([v (in-vector V 1)]
              [i (in-naturals 1)])
             (fl* v (fl i)))
           (- n 1))]))
     (make-flpoly (inner (flpoly-v P) n) d*)]))
(module+ test
  (check-equal? (flpoly-diff (flpoly> 1.0 1.0 1.0 1.0) 1) (flpoly> 3.0 2.0 1.0))
  (check-equal? (flpoly-diff (flpoly> 1.0 1.0 1.0 1.0) 2) (flpoly> 6.0 2.0))
  (check-equal? (flpoly-diff (flpoly> 1.0 1.0) 3) flpoly-zero))

(: flpoly-int (->* (flpoly) (Nonnegative-Integer) flpoly))
(define (flpoly-int P [n 1]) : flpoly
  (cond
    [(= n 0) (flpoly-copy P)]
    [else
     (flpoly-int
      (flpoly-shift
       (make-flpoly
        (for/vector : (Vectorof Flonum)
          ([v (in-vector (flpoly-v P))]
           [i (in-naturals 1)])
          (fl/ v (fl i)))
        (flpoly-degree P))
       1)
      (- n 1))]))
(module+ test
  (check-equal? (flpoly-int (flpoly> 1.0 1.0 1.0 1.0) 1) (flpoly> (fl 1/4) (fl 1/3) (fl 1/2) 1.0 0.0))
  (check-equal? (flpoly-int (flpoly> 1.0 1.0 1.0) 2) (flpoly> (fl 1/12) (fl 1/6) (fl 1/2) 0.0 0.0)))

;------------------------------------
;division
;------------------------------------
(define (flpoly/p-QR [P : flpoly] [/p : flpoly]) : (Values flpoly flpoly)
  (define dn (flpoly-degree P))
  (define dd (flpoly-degree /p))
  (define dQ (- dn dd))
  (cond
    [(< dQ 0)
     (values flpoly-zero (flpoly-copy P))]
    [(= dd 0)
     (values (flpoly*s P (fl/ 1.0 (flpoly-coefficient /p 0))) flpoly-zero)]
    [else
     (define R (vector-copy (flpoly-v P)))
     (define Q (make-vector (+ dQ 1) 0.0))
     (for ([k (in-range dQ -1 -1)])
       (vector-set! Q k (fl/ (vector-ref R (+ dd k))
                             (flpoly-coefficient /p dd)))
       (for ([j (in-range (+ dd k -1) (- k 1) -1)])
         (vector-set! R j (fl- (vector-ref R j)
                               (fl* (vector-ref Q k)
                                    (flpoly-coefficient /p (- j k)))))))
     (values (make-flpoly Q dQ)
             (flpolyV< (vector-take R dd)))]))
(module+ test
  (let ([P (flpoly> 1.0 2.0 1.0)]
        [/p (flpoly> 1.0 1.0)])
    (define-values (Q R) (flpoly/p-QR P /p))
    (check-equal? Q (flpoly> 1.0 1.0))
    (check-equal? (flpoly-degree R) 0)
    (check-= (flpoly-coefficient R 0) 0 1e-16))
  (let ([P (flpoly> 1.0 3.0 3.0 1.0)]
        [/p (flpoly> 1.0 1.0)])
    (define-values (Q R) (flpoly/p-QR P /p))
    (check-equal? Q (flpoly> 1.0 2.0 1.0))
    (check-equal? (flpoly-degree R) 0)
    (check-= (flpoly-coefficient R 0) 0 1e-16))
  (let ([P (flpoly> 1.0 3.0 4.0 2.0)]
        [/p (flpoly> 1.0 2.0 1.0)])
    (define-values (Q R) (flpoly/p-QR P /p))
    (check-equal? Q (flpoly> 1.0 1.0))
    (check-equal? R (flpoly> 1.0 1.0))))

(define (flpoly-reduce-root-QR [P : flpoly] [r : Flonum]) : (Values flpoly Flonum)
  (define d (flpoly-degree P))
  (cond
    [(<= d 0)(raise-argument-error 'flpoly-reduce-root "No roots for poly of degree 0" P)]
    [else
     (define v : (Vectorof Flonum) (make-vector d 0.0))
     (define s
       (for/fold ([s : Flonum (flpoly-coefficient P d)])
                 ([i (in-range (- d 1) -1 -1)])
         (vector-set! v i s)
         (define s+ (fl+ (* r s) (flpoly-coefficient P i)))
         s+))
     (values (make-flpoly v (- d 1)) s)]))
(module+ test
  (let ([P (flpoly> 1.0 2.0 1.0)]
        [r -1.0])
    (define-values (Q R) (flpoly-reduce-root-QR P r))
    (check-equal? Q (flpoly> 1.0 1.0))
    (check-= R 0 1e-16))
  (let ([P (flpoly> 1.0 3.0 3.0 1.0)]
        [r -1.0])
    (define-values (Q R) (flpoly-reduce-root-QR P r))
    (check-equal? Q (flpoly> 1.0 2.0 1.0))
    (check-= R 0 1e-16))
  (let ([P (flpoly> 5.0 2.0 -3.0)]
        [r 3.0])
    (define-values (Q R) (flpoly-reduce-root-QR P r))
    (check-equal? Q (flpoly> 5.0 17.0))
    (check-= R 48 1e-16)))

;------------------------------------
;absolute coefficient
;------------------------------------
(define (flpoly->absolute-coefficients [P : flpoly])
  (make-flpoly (for/vector : (Vectorof Flonum)([v : Flonum(in-vector (flpoly-v P))])(abs v))
               (flpoly-degree P)))
(module+ test
  (check-equal? (flpoly->absolute-coefficients (flpoly> -1.0 2.0 -1.0)) (flpoly> 1.0 2.0 1.0)))

;------------------------------------
;checking how much improvement the Horner/Horner+/compensatedHorner brings
;anecdotal evidence:
; bigger t (farther from the roots) compensatedHorner wins out
;smaller t (arround roots) Horner+ is the winner (and on average is more accurate than Horner)
;------------------------------------
#;(module+ test
  (require math/bigfloat)
  (define (bfHorner [P : flpoly] [t : Flonum])
    (define T (bf t))
    (for/fold : Bigfloat
      ([sum : Bigfloat (bf 0.0)])
      ([ai ((inst in-vector Flonum) (flpoly-v P) (flpoly-degree P) -1 -1)])
      (bf+ (bf* sum T) (bf ai))))
  ;(define P (flpoly< 1.0 0.0 0.0002 -0.0004 0.0 -1.0))(define a 0.0)(define b 20.0)
  (define P (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))(define a -0.183500)(define b -0.183507)
  
  (define a->b (/ (- b a) 1000.0))
  (define (mfl1 [t : Flonum]) : Flonum (Horner P t))
  (define (mfl2 [t : Flonum]) : Bigfloat (bfHorner P t))
  (define (mfl3 [t : Flonum]) : Flonum (compensatedHorner P t))
  (define (mfl4 [t : Flonum]) : Flonum (Horner+ P t))
  (define (errdiff [t : Flonum])
    (bigfloat->flonum
     (bf-
      (bfabs
       (bf- (mfl2 t)
            (bf (mfl3 t))));error with comp horner
      (bfabs
       (bf- (mfl2 t)
            (bf (mfl1 t))));error with reg horner
      ;if sum is neg -> reg horner error on avarage bigger than comp horner
      )))
  (define (test [t0 : Flonum] [t1 : Flonum] [n : Integer 10000]) : Flonum
    (/
     (for/fold : Flonum
       ([s : Flonum 0.0])
       ([i (in-range n)])
       (define t (+ 0.99 (* 1.01 (random))))
       (fl+ s (errdiff t)))
     n))
  (test .99 1.01)
  (test 0.0 .99)
  (test -4.0 4.0)
  (test -4.0 0.0)
  (test 2.0 6.0)
  (test 2.0 10.0)
  (require plot)
  (plot
   (list
    (function (λ ([T : Real]) (errdiff (fl T))) a b)
    (x-axis)))
  #;(plot
   (list
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl3 (fl t)))));error with comp horner
                 ))
              a b #:color 'blue)
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl1 (fl t)))));error with reg horner
                 ))
              a b)
    (function (λ ([t : Real])
                (bigfloat->flonum
                 (bfabs
                  (bf- (mfl2 (fl t))
                       (bf (mfl4 (fl t)))));error with horner+
                 ))
              a b #:color 'green)
    (x-axis)))
  (plot
   (list
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl3 (fl t)))));error with comp horner
                     ))) #:size 1 #:color 'blue)
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl1 (fl t)))));error with reg horner
                     ))) #:size 1 #:color 1)
    (points (for/list : (Listof (List Flonum Flonum))
              ([t : Flonum (in-range a b a->b)])
              (list t
                    (bigfloat->flonum
                     (bfabs
                      (bf- (mfl2 (fl t))
                           (bf (mfl4 (fl t)))));error with horner+
                     ))) #:size 1 #:color 'green)
    (x-axis))))
#;(module+ test
  (require plot)
  (define P (flpoly-from-roots -2.632993161855452 -0.18350341907227397 -0.18350341907227397))(define a -0.183500)(define b -0.183507)
  (plot (list (function (λ ([x : Real])(Horner P (fl x))) a b #:color 1)
              (function (λ ([x : Real])(Horner+ P (fl x))) a b #:color 2)
              (function (λ ([x : Real])(compensatedHorner P (fl x))) a b #:color 3))))