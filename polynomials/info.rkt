#lang info

(define collection 'multi)

(define deps '("racket/base" "math-lib" "math-doc"))
(define implies '("math-lib" "math-doc"))
(define build-deps '("rackunit"))

(define pkg-desc "Adds polynomials to the math collection")

