#lang scribble/manual

@(require scribble/eval
          racket/sandbox
          (for-label racket/base
                     math plot
                     math/polynomials
                     (only-in typed/racket/base
                              Any Boolean Vectorof Listof Number Integer Nonnegative-Integer
                              Exact-Rational Exact-Number Flonum Float-Complex))
          math/scribblings/utils)

@(define untyped-eval (make-untyped-math-eval))
@interaction-eval[#:eval untyped-eval (require math/polynomials)]

@title[#:tag "polynomials"]{Polynomials}

@defmodule[math/polynomials]

This library provides basic tools for calculations with polynomials.
Polynomials are expressions of the form: a0.x^0+a1.x^1+a2.x^2+...+an.x^n. With n the degree
of the polynomial.

@local-table-of-contents[]


@;{==================================================================================================}


@section[#:tag "polynomials:types"]{Types, Predicates and Accessors}

For now the polynomial is defined in 4 varieties. Exact-Rational: @racket[epoly?], Real: @racket[flpoly?],
Exact-Complex @racket[ecpoly?] and Float-Complex @racket[flcpoly?]. In what follows usually only the general poly functions are
described. For specific ones add e,fl,ec or flc to poly.

@deftogether[(@defproc[(poly? [P Any]) Boolean]
              @defproc[(epoly? [P Any]) Boolean]
              @defproc[(flpoly? [P Any]) Boolean]
              @defproc[(ecpoly? [P Any]) Boolean]
              @defproc[(flcpoly? [P Any]) Boolean])]
Poly predicate.

@defproc[(poly-v [P poly?]) (Vectorof Number)]
The coefficients of the polynomial, ordened from small to large degree.

@deftogether[(@defproc[(poly-degree [P poly?]) Nonnegative-Integer]
              @defproc[(poly-size [P poly?])   Nonnegative-Integer])]
Return the degree or the size of the coefficient-vector for the polynomial. The size is degree+1.

@deftogether[(@defproc[(poly-coefficient [P poly?][i Integer]) Number]
              @defproc[(poly-reverse-coefficient [P poly?][i Integer])   Number])]
Get coefficient at position i. If i is too large or to small, 0 will be returned. The reverse form
will return the coefficient starting from the highest degree. In other words:
@racket[(poly-reverse-coefficient P i)] is equivalent with @racket[(poly-coefficient P (- degree i))]

@;{==================================================================================================}


@section[#:tag "polynomials:construction"]{Construction}

@deftogether[(@defproc[(polyV< [V (Vectorof Number)]) poly?]
              @defproc[(polyL< [L (Listof Number)])   poly?]
              @defproc[(poly<  [a Number] ...)        poly?]
              @defproc[(polyV> [V (Vectorof Number)]) poly?]
              @defproc[(polyL> [L (Listof Number)])   poly?]
              @defproc[(poly>  [a Number] ...)        poly?])]
Create a polynomial by vector, list or individual arguments. Coefficient of biggest degree last (>) or first (<).

The specific constructors are:
@deftogether[(@defproc[(epoly>   [a Exact-Rational] ...) epoly?]
              @defproc[(flpoly>  [a Flonum] ...)         flpoly?]
              @defproc[(ecpoly>  [a Exact-Number] ...)   ecpoly?]
              @defproc[(flcpoly> [a Float-Complex] ...)  flcpoly?])]


@defproc[(poly-const [a Number]) poly?]
Creates a polynomial of degree 0.

@deftogether[(@defthing[poly-zero poly?]
              @defthing[poly-one  poly?])]
Constant polynomial 0 and 1.

@defproc[(poly-from-roots [#:s s Number] [r Number] ...) poly?]
Create a polynomial from its roots. When trying to create a Real polynomial, the conjugate complex roots
must both be specified with the same precision.

@defproc[(poly-copy [P poly?]) poly?]
Creates a copy.

@defproc[(poly->absolute-coefficients [P poly?]) poly?]
Returns a polynomial with all coefficients positive. (Not for complex polynomials.)

@;{==================================================================================================}


@section[#:tag "polynomials:eval"]{Evaluation}
@defproc[(Horner [P poly?] [x Number]) Number]
Evaluate the polynomial in x.

@deftogether[(@defproc[(flHorner+ [P flpoly?] [x Flonum]) Flonum]
              @defproc[(compensatedflHorner [P flpoly?] [x Flonum]) Flonum])]
For flonums these functions give better results by avoiding rounding errors.
flHorner+ is generally more accurate than Horner, compensatedflHorner is a lot better for values far from
the origin, but performs slightly worse around the origin.

                                                                                  
@;{==================================================================================================}


@section[#:tag "polynomials:base"]{Basic operations}

@defproc[(poly*s [P1 poly?] [s Number]) poly?]
Multiply the polynomial by a scalar

@deftogether[(@defproc[(poly+ [P1 poly?][P2 poly?] ...) poly?]
              @defproc[(poly- [P1 poly?][P2 poly?] ...) poly?]
              @defproc[(poly* [P1 poly?][P2 poly?] ...) poly?]
              @defproc[(poly-expt [P1 poly] [e Nonnegative-Integer]) poly?])]
Basic operations + - * expt for polynomials.

@defproc[(flpoly*-accurate [P1 flpoly?][P2 flpoly?] ...) flpoly?]
flpoly*-accurate agregates all terms of the intermediate sums first.
Reducing rounding error at the price of speed (factor 3).

@defproc[(poly/p-QR [P1 poly?][P2 poly?]) (Values poly? poly?)]
Divides P1 by P2 returning the quotient and remainder.

@defproc[(poly-reduce-root-QR [P1 poly?][r Number]) (Values poly? Number)]
Divides P1 by @racket[(poly-from-roots r)] returning the quotient and remainder.

@defproc[(poly-subst [P1 poly?][P2 poly?]) poly?]
Substitute the variable x of P1 by P2

@defproc[(poly-shift [P1 poly?][i Integer]) poly?]
Shift the coefficients of P1 up or down. Coefficients with an index lower than zero will be dropped.
As far as no coefficients are dropped, this is equal to multiplying/deviding by x^i.

@deftogether[(@defproc[(poly-diff [P1 poly?] [i Nonnegative-Integer 1]) poly?]
              @defproc[(poly-int [P1 poly?] [i Nonnegative-Integer 1]) poly?])]
Take the i-th differential/integral of the polynomial.



                                                                                  
@;{==================================================================================================}


@section[#:tag "polynomials:roots"]{Root finding algorithms}

TODO:write doc



@;{==================================================================================================}
@(close-eval untyped-eval)
