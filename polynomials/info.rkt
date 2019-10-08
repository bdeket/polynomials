#lang info

(define collection 'multi)

(define deps '("racket/base"
               "typed-racket-lib"
               "math-lib"
			   "math-doc"))
(define implies '("math-lib"
                  "math-doc"))
(define build-deps '("rackunit"
					 "rackunit-typed"
					 
                     "scribble-lib"
                     "racket-doc"
					 "typed-racket-doc"
					 "plot-gui-lib"
					 "sandbox-lib"))

(define pkg-desc "Adds polynomials to the math collection")

