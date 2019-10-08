#lang scribble/manual

@(require scribble/eval
          racket/sandbox
          (for-label racket/base
                     math plot
                     (only-in typed/racket/base
                              Exact-Rational Exact-Number Flonum Float-Complex))
          math/scribblings/utils)

@(define untyped-eval (make-untyped-math-eval))
@interaction-eval[#:eval untyped-eval (require math/polynomials)]

@title[#:tag "polynomials"]{Polynomials}

@defmodule[math/polynomials]

This library provides basic tools for calculations with polynomials

@local-table-of-contents[]


@;{==================================================================================================}


@section[#:tag "polynomials:intro"]{Introduction}

Polynomials are expressions of the form: a0.x^0+a1.x^1+a2.x^2+...+an.x^n. With n the degree
of the polynomial.


@;{==================================================================================================}


@section[#:tag "polynomials:types"]{Types, Predicates and Accessors}

@defform[(Matrix A)]{
Equivalent to @racket[(Array A)], but used for values @racket[M] for which @racket[(matrix? M)] is
@racket[#t].
}



@;{==================================================================================================}


@section[#:tag "polynomials:construction"]{Construction}



@;{==================================================================================================}


@section[#:tag "polynomials:eval"]{Evaluation}

                                                                                  
@;{==================================================================================================}


@section[#:tag "polynomials:base"]{Basic operations}

                                                                                  
@;{==================================================================================================}


@section[#:tag "polynomials:roots"]{Root finding algorithms}

@deftogether[(@defproc[(matrix+ [M (Matrix Number)] [N (Matrix Number)] ...) (Matrix Number)]
              @defproc[(matrix- [M (Matrix Number)] [N (Matrix Number)] ...) (Matrix Number)]
              @defproc[(matrix* [M (Matrix Number)] [N (Matrix Number)] ...) (Matrix Number)])]{
Matrix addition, subtraction and products respectively.

For matrix addition and subtraction all matrices must have the same shape.

For matrix product the number of columns of one matrix must equal the 
number of rows in the following matrix.

@examples[#:eval untyped-eval
                 (define A (matrix ([1 2] 
                                    [3 4])))
                 (define B (matrix ([5 6] 
                                    [7 8])))
                 (define C (matrix ([ 9 10 11]
                                    [12 13 14])))
                 (matrix+ A B)
                 (matrix- A B)
                 (matrix* A C)]
}

@defproc[(matrix-expt [M (Matrix Number)] [n Integer]) (Matrix Number)]{
Computes @racket[(matrix* M ...)] with @racket[n] arguments, but more efficiently.
@racket[M] must be a @racket[square-matrix?] and @racket[n] must be nonnegative.
@examples[#:eval untyped-eval
                 ; The 100th (and 101th) Fibonacci number:
                 (matrix* (matrix-expt (matrix [[1 1] [1 0]]) 100)
                          (col-matrix [0 1]))
                 (->col-matrix (list (fibonacci 100) (fibonacci 99)))]
}
@(close-eval untyped-eval)
