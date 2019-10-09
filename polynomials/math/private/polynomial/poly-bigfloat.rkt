#lang typed/racket/base

(require math/bigfloat)
(require "poly-mbase.rkt")

  
(struct bf-complex ([r : Bigfloat][i : Bigfloat]) #:transparent)
(define-type Bigfloat-Complex (U Bigfloat bf-complex))
(define (bf-real [e : Bigfloat-Complex])(if (bigfloat? e)  e     (bf-complex-r e)))
(define (bf-imag [e : Bigfloat-Complex])(if (bigfloat? e) (bf 0) (bf-complex-i e)))
(define i.bf (bf-complex (bf 0) (bf 1)))
(define (bfsum [L : (Listof Bigfloat)])(apply bf+ L))

(make-poly-base bf Bigfloat
                bf bf= bf+ bf- bf* bf/ bfsum)
(make-poly-realfct bf Bigfloat
                   bfpoly bfpoly-v bfpoly-degree bfpoly*
                   Bigfloat-Complex bf-real bf-imag bf-complex
                   bf bf= bf+ bf- bf* bf/
                   bfsum bfabs)

(module+ test
  (bfpoly-const (bf 3/8))
  bfpoly-zero
  bfpoly-one
  (bfpoly-copy bfpoly-zero)
  (bfpolyV< (vector (bf 0) (bf 1) (bf 2) (bf 3/4) (bf 0)))
  (bfpoly> (bf 5) (bf 4) (bf 3) (bf 2) (bf 1) (bf 0))

  (bfpoly+ (bfpoly> (bf 5) (bf 4) (bf 3) (bf 2) (bf 1) (bf 0))
           (bfpoly> (bf 0) (bf 1) (bf 2) (bf 3) (bf 4) (bf 5))
           (bfpoly> (bf 1) (bf 3) (bf 5) (bf 5) (bf 3) (bf 1)))

  (bfpoly* (bfpoly> (bf 5) (bf 4) (bf 3) (bf 2) (bf 1) (bf 0))
           (bfpoly> (bf 0) (bf 1) (bf 2) (bf 3) (bf 4) (bf 5))
           (bfpoly> (bf 1) (bf 3) (bf 5) (bf 5) (bf 3) (bf 1)))

  (bfpoly-from-roots  (bf 9998/1000)
                      (bf 9999/1000)
                      (bf 1)
                      (bf 10003/1000)
                      (bf 10003/1000))

  (bfpoly-reduce-root-QR (bfpoly-from-roots  (bf 9998/1000)
                                             (bf 9999/1000)
                                             (bf 1)
                                             (bf 10003/1000)
                                             (bf 10003/1000))
                         (bf 1))

  (bfpoly-reduce-root-QR (bfpoly-from-roots  (bf 9998/1000)
                                             (bf 9999/1000)
                                             (bf 1)
                                             (bf 10003/1000)
                                             (bf 10003/1000))
                         (bf 9998/1000))

  (bfpoly-from-roots (bf 1/2)
                     (bf-complex (bf 1/3) (bf 1/4))
                     (bf-complex (bf 1/3) (bf -1/4))))
